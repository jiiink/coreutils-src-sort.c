/* sort - sort lines of text (with all kinds of options).
   Copyright (C) 1988-2025 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

   Written December 1988 by Mike Haertel.
   The author may be reached (Email) at the address mike@gnu.ai.mit.edu,
   or (US mail) as Mike Haertel c/o Free Software Foundation.

   Ørn E. Hansen added NLS support in 1997.  */

#include <config.h>

#include <ctype.h>
#include <getopt.h>
#include <pthread.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include "system.h"
#include "argmatch.h"
#include "assure.h"
#include "c-ctype.h"
#include "fadvise.h"
#include "filevercmp.h"
#include "flexmember.h"
#include "hard-locale.h"
#include "hash.h"
#include "heap.h"
#include "ignore-value.h"
#include "mbswidth.h"
#include "nproc.h"
#include "physmem.h"
#include "posixver.h"
#include "quote.h"
#include "randread.h"
#include "readtokens0.h"
#include "stdlib--.h"
#include "strnumcmp.h"
#include "xmemcoll.h"
#include "xnanosleep.h"
#include "xstrtol.h"
#include "xstrtol-error.h"

#ifndef RLIMIT_DATA
struct rlimit { size_t rlim_cur; };
# define getrlimit(Resource, Rlp) (-1)
#endif

/* The official name of this program (e.g., no 'g' prefix).  */
#define PROGRAM_NAME "sort"

#define AUTHORS \
  proper_name ("Mike Haertel"), \
  proper_name ("Paul Eggert")

#if HAVE_LANGINFO_CODESET
# include <langinfo.h>
#endif

/* Use SA_NOCLDSTOP as a proxy for whether the sigaction machinery is
   present.  */
#ifndef SA_NOCLDSTOP
# define SA_NOCLDSTOP 0
/* No sigprocmask.  Always 'return' zero. */
# define sigprocmask(How, Set, Oset) (0)
# define sigset_t int
# if ! HAVE_SIGINTERRUPT
#  define siginterrupt(sig, flag) /* empty */
# endif
#endif

#if !defined OPEN_MAX && defined NR_OPEN
# define OPEN_MAX NR_OPEN
#endif
#if !defined OPEN_MAX
# define OPEN_MAX 20
#endif

#define UCHAR_LIM (UCHAR_MAX + 1)

#ifndef DEFAULT_TMPDIR
# define DEFAULT_TMPDIR "/tmp"
#endif

/* Maximum number of lines to merge every time a NODE is taken from
   the merge queue.  Node is at LEVEL in the binary merge tree,
   and is responsible for merging TOTAL lines. */
#define MAX_MERGE(total, level) (((total) >> (2 * ((level) + 1))) + 1)

/* Heuristic value for the number of lines for which it is worth creating
   a subthread, during an internal merge sort.  I.e., it is a small number
   of "average" lines for which sorting via two threads is faster than
   sorting via one on an "average" system.  On a dual-core 2.0 GHz i686
   system with 3GB of RAM and 2MB of L2 cache, a file containing 128K
   lines of gensort -a output is sorted slightly faster with --parallel=2
   than with --parallel=1.  By contrast, using --parallel=1 is about 10%
   faster than using --parallel=2 with a 64K-line input.  */
enum { SUBTHREAD_LINES_HEURISTIC = 128 * 1024 };
static_assert (4 <= SUBTHREAD_LINES_HEURISTIC);

/* The number of threads after which there are
   diminishing performance gains.  */
enum { DEFAULT_MAX_THREADS = 8 };

/* Exit statuses.  */
enum
  {
    /* POSIX says to exit with status 1 if invoked with -c and the
       input is not properly sorted.  */
    SORT_OUT_OF_ORDER = 1,

    /* POSIX says any other irregular exit must exit with a status
       code greater than 1.  */
    SORT_FAILURE = 2
  };

enum
  {
    /* The number of times we should try to fork a compression process
       (we retry if the fork call fails).  We don't _need_ to compress
       temp files, this is just to reduce file system access, so this number
       can be small.  Each retry doubles in duration.  */
    MAX_FORK_TRIES_COMPRESS = 4,

    /* The number of times we should try to fork a decompression process.
       If we can't fork a decompression process, we can't sort, so this
       number should be big.  Each retry doubles in duration.  */
    MAX_FORK_TRIES_DECOMPRESS = 9
  };

enum
  {
    /* Level of the end-of-merge node, one level above the root. */
    MERGE_END = 0,

    /* Level of the root node in merge tree. */
    MERGE_ROOT = 1
  };

/* The representation of the decimal point in the current locale.  */
static char decimal_point;

/* Thousands separator; if outside char range, there is no separator.  */
static int thousands_sep;
/* We currently ignore multi-byte grouping chars.  */
static bool thousands_sep_ignored;

/* Nonzero if the corresponding locales are hard.  */
static bool hard_LC_COLLATE;
#if HAVE_NL_LANGINFO
static bool hard_LC_TIME;
#endif

#define NONZERO(x) ((x) != 0)

/* The kind of blanks for '-b' to skip in various options. */
enum blanktype { bl_start, bl_end, bl_both };

/* The character marking end of line. Default to \n. */
static char eolchar = '\n';

/* Lines are held in memory as counted strings. */
struct line
{
  char *text;			/* Text of the line. */
  size_t length;		/* Length including final newline. */
  char *keybeg;			/* Start of first key. */
  char *keylim;			/* Limit of first key. */
};

/* Input buffers. */
struct buffer
{
  char *buf;			/* Dynamically allocated buffer,
                                   partitioned into 3 regions:
                                   - input data;
                                   - unused area;
                                   - an array of lines, in reverse order.  */
  size_t used;			/* Number of bytes used for input data.  */
  size_t nlines;		/* Number of lines in the line array.  */
  idx_t alloc;			/* Number of bytes allocated. */
  size_t left;			/* Number of bytes left from previous reads. */
  size_t line_bytes;		/* Number of bytes to reserve for each line. */
  bool eof;			/* An EOF has been read.  */
};

/* Sort key.  */
struct keyfield
{
  size_t sword;			/* Zero-origin 'word' to start at. */
  size_t schar;			/* Additional characters to skip. */
  size_t eword;			/* Zero-origin last 'word' of key. */
  size_t echar;			/* Additional characters in field. */
  bool const *ignore;		/* Boolean array of characters to ignore. */
  char const *translate;	/* Translation applied to characters. */
  bool skipsblanks;		/* Skip leading blanks when finding start.  */
  bool skipeblanks;		/* Skip leading blanks when finding end.  */
  bool numeric;			/* Flag for numeric comparison.  Handle
                                   strings of digits with optional decimal
                                   point, but no exponential notation. */
  bool random;			/* Sort by random hash of key.  */
  bool general_numeric;		/* Flag for general, numeric comparison.
                                   Handle numbers in exponential notation. */
  bool human_numeric;		/* Flag for sorting by human readable
                                   units with either SI or IEC prefixes. */
  bool month;			/* Flag for comparison by month name. */
  bool reverse;			/* Reverse the sense of comparison. */
  bool version;			/* sort by version number */
  bool traditional_used;	/* Traditional key option format is used. */
  struct keyfield *next;	/* Next keyfield to try. */
};

struct month
{
  char const *name;
  int val;
};

/* Binary merge tree node. */
struct merge_node
{
  struct line *lo;              /* Lines to merge from LO child node. */
  struct line *hi;              /* Lines to merge from HI child node. */
  struct line *end_lo;          /* End of available lines from LO. */
  struct line *end_hi;          /* End of available lines from HI. */
  struct line **dest;           /* Pointer to destination of merge. */
  size_t nlo;                   /* Total Lines remaining from LO. */
  size_t nhi;                   /* Total lines remaining from HI. */
  struct merge_node *parent;    /* Parent node. */
  struct merge_node *lo_child;  /* LO child node. */
  struct merge_node *hi_child;  /* HI child node. */
  unsigned int level;           /* Level in merge tree. */
  bool queued;                  /* Node is already in heap. */
  pthread_mutex_t lock;         /* Lock for node operations. */
};

/* Priority queue of merge nodes. */
struct merge_node_queue
{
  struct heap *priority_queue;  /* Priority queue of merge tree nodes. */
  pthread_mutex_t mutex;        /* Lock for queue operations. */
  pthread_cond_t cond;          /* Conditional wait for empty queue to populate
                                   when popping. */
};

/* Used to implement --unique (-u).  */
static struct line saved_line;

/* FIXME: None of these tables work with multibyte character sets.
   Also, there are many other bugs when handling multibyte characters.
   One way to fix this is to rewrite 'sort' to use wide characters
   internally, but doing this with good performance is a bit
   tricky.  */

/* Table of blanks.  */
static bool blanks[UCHAR_LIM];

/* Table of non-printing characters. */
static bool nonprinting[UCHAR_LIM];

/* Table of non-dictionary characters (not letters, digits, or blanks). */
static bool nondictionary[UCHAR_LIM];

/* Translation table folding lower case to upper.  */
static char fold_toupper[UCHAR_LIM];

#define MONTHS_PER_YEAR 12

/* Table mapping month names to integers.
   Alphabetic order allows binary search. */
static struct month monthtab[] =
{
  {"APR", 4},
  {"AUG", 8},
  {"DEC", 12},
  {"FEB", 2},
  {"JAN", 1},
  {"JUL", 7},
  {"JUN", 6},
  {"MAR", 3},
  {"MAY", 5},
  {"NOV", 11},
  {"OCT", 10},
  {"SEP", 9}
};

/* During the merge phase, the number of files to merge at once. */
#define NMERGE_DEFAULT 16

/* Minimum size for a merge or check buffer.  */
#define MIN_MERGE_BUFFER_SIZE (2 + sizeof (struct line))

/* Minimum sort size; the code might not work with smaller sizes.  */
#define MIN_SORT_SIZE (nmerge * MIN_MERGE_BUFFER_SIZE)

/* The number of bytes needed for a merge or check buffer, which can
   function relatively efficiently even if it holds only one line.  If
   a longer line is seen, this value is increased.  */
static size_t merge_buffer_size = MAX (MIN_MERGE_BUFFER_SIZE, 256 * 1024);

/* The approximate maximum number of bytes of main memory to use, as
   specified by the user.  Zero if the user has not specified a size.  */
static size_t sort_size;

/* The initial allocation factor for non-regular files.
   This is used, e.g., when reading from a pipe.
   Don't make it too big, since it is multiplied by ~130 to
   obtain the size of the actual buffer sort will allocate.
   Also, there may be 8 threads all doing this at the same time.  */
#define INPUT_FILE_SIZE_GUESS (128 * 1024)

/* Array of directory names in which any temporary files are to be created. */
static char const **temp_dirs;

/* Number of temporary directory names used.  */
static idx_t temp_dir_count;

/* Number of allocated slots in temp_dirs.  */
static idx_t temp_dir_alloc;

/* Flag to reverse the order of all comparisons. */
static bool reverse;

/* Flag for stable sort.  This turns off the last ditch bytewise
   comparison of lines, and instead leaves lines in the same order
   they were read if all keys compare equal.  */
static bool stable;

/* An int value outside char range.  */
enum { NON_CHAR = CHAR_MAX + 1 };

/* If TAB has this value, blanks separate fields.  */
enum { TAB_DEFAULT = CHAR_MAX + 1 };

/* Tab character separating fields.  If TAB_DEFAULT, then fields are
   separated by the empty string between a non-blank character and a blank
   character. */
static int tab = TAB_DEFAULT;

/* Flag to remove consecutive duplicate lines from the output.
   Only the last of a sequence of equal lines will be output. */
static bool unique;

/* Nonzero if any of the input files are the standard input. */
static bool have_read_stdin;

/* List of key field comparisons to be tried.  */
static struct keyfield *keylist;

/* Program used to (de)compress temp files.  Must accept -d.  */
static char const *compress_program;

/* Annotate the output with extra info to aid the user.  */
static bool debug;

/* Maximum number of files to merge in one go.  If more than this
   number are present, temp files will be used. */
static unsigned int nmerge = NMERGE_DEFAULT;

/* Output an error to stderr and exit using async-signal-safe routines.
   This can be used safely from signal handlers,
   and between fork and exec of multithreaded processes.  */

static _Noreturn void
async_safe_die (int errnum, char const *errstr)
{
  if (errstr)
    {
      ignore_value (write (STDERR_FILENO, errstr, strlen (errstr)));
    }

  if (errnum)
    {
      char num_buf[INT_BUFSIZE_BOUND (errnum)];
      char *num_str = inttostr (errnum, num_buf);

      ignore_value (write (STDERR_FILENO, ": errno ", sizeof ": errno " - 1));
      ignore_value (write (STDERR_FILENO, num_str, strlen (num_str)));
    }

  ignore_value (write (STDERR_FILENO, "\n", sizeof "\n" - 1));

  _exit (SORT_FAILURE);
}

/* Report MESSAGE for FILE, then clean up and exit.
   If FILE is null, it represents standard output.  */

static void
sort_die (char const *message, char const *file)
{
  char const *name = file ? file : _("standard output");
  error (SORT_FAILURE, errno, "%s: %s", message, quotef (name));
}

static void
print_usage_synopsis (void)
{
  printf (_("\
Usage: %s [OPTION]... [FILE]...\n\
  or:  %s [OPTION]... --files0-from=F\n\
"),
          program_name, program_name);
  fputs (_("\
Write sorted concatenation of all FILE(s) to standard output.\n\
"), stdout);

  emit_stdin_note ();
  emit_mandatory_arg_note ();
}

static void
print_ordering_options (void)
{
  fputs (_("\
Ordering options:\n\
\n\
  -b, --ignore-leading-blanks  ignore leading blanks\n\
  -d, --dictionary-order      consider only blanks and alphanumeric characters\
\n\
  -f, --ignore-case           fold lower case to upper case characters\n\
  -g, --general-numeric-sort  compare according to general numerical value\n\
  -i, --ignore-nonprinting    consider only printable characters\n\
  -M, --month-sort            compare (unknown) < 'JAN' < ... < 'DEC'\n\
  -h, --human-numeric-sort    compare human readable numbers (e.g., 2K 1G)\n\
  -n, --numeric-sort          compare according to string numerical value;\n\
                                see full documentation for supported strings\n\
  -R, --random-sort           shuffle, but group identical keys.  See shuf(1)\n\
      --random-source=FILE    get random bytes from FILE\n\
  -r, --reverse               reverse the result of comparisons\n\
      --sort=WORD             sort according to WORD:\n\
                                general-numeric -g, human-numeric -h, month -M,\
\n\
                                numeric -n, random -R, version -V\n\
  -V, --version-sort          natural sort of (version) numbers within text\n\
\n\
"), stdout);
}

static void
print_other_options (void)
{
  fputs (_("\
Other options:\n\
\n\
      --batch-size=NMERGE   merge at most NMERGE inputs at once;\n\
                            for more use temp files\n\
  -c, --check, --check=diagnose-first  check for sorted input; do not sort\n\
  -C, --check=quiet, --check=silent  like -c, but do not report first bad line\
\n\
      --compress-program=PROG  compress temporaries with PROG;\n\
                              decompress them with PROG -d\n\
      --debug               annotate the part of the line used to sort, and\n\
                              warn about questionable usage to standard error\n\
      --files0-from=F       read input from the files specified by\n\
                            NUL-terminated names in file F;\n\
                            If F is - then read names from standard input\n\
  -k, --key=KEYDEF          sort via a key; KEYDEF gives location and type\n\
  -m, --merge               merge already sorted files; do not sort\n\
  -o, --output=FILE         write result to FILE instead of standard output\n\
  -s, --stable              stabilize sort by disabling last-resort comparison\
\n\
  -S, --buffer-size=SIZE    use SIZE for main memory buffer\n\
"), stdout);
  printf (_("\
  -t, --field-separator=SEP  use SEP instead of non-blank to blank transition\n\
  -T, --temporary-directory=DIR  use DIR for temporaries, not $TMPDIR or %s;\n\
                              multiple options specify multiple directories\n\
      --parallel=N          change the number of sorts run concurrently to N\n\
  -u, --unique              output only the first of lines with equal keys;\n\
                              with -c, check for strict ordering\n\
"), DEFAULT_TMPDIR);
  fputs (_("\
  -z, --zero-terminated     line delimiter is NUL, not newline\n\
"), stdout);

  fputs (HELP_OPTION_DESCRIPTION, stdout);
  fputs (VERSION_OPTION_DESCRIPTION, stdout);
}

static void
print_notes (void)
{
  fputs (_("\
\n\
KEYDEF is F[.C][OPTS][,F[.C][OPTS]] for start and stop position, where F is a\n\
field number and C a character position in the field; both are origin 1, and\n\
the stop position defaults to the line's end.  If neither -t nor -b is in\n\
effect, characters in a field are counted from the beginning of the preceding\n\
whitespace.  OPTS is one or more single-letter ordering options [bdfgiMhnRrV],\
\n\
which override global ordering options for that key.  If no key is given, use\n\
the entire line as the key.  Use --debug to diagnose incorrect key usage.\n\
\n\
SIZE may be followed by the following multiplicative suffixes:\n\
% 1% of memory, b 1, K 1024 (default), and so on for M, G, T, P, E, Z, Y, R, Q.\
\n\n\
*** WARNING ***\n\
The locale specified by the environment affects sort order.\n\
Set LC_ALL=C to get the traditional sort order that uses\n\
native byte values.\n\
"), stdout);
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      emit_try_help ();
    }
  else
    {
      print_usage_synopsis ();
      print_ordering_options ();
      print_other_options ();
      print_notes ();
      emit_ancillary_info (PROGRAM_NAME);
    }

  exit (status);
}

/* For long options that have no equivalent short option, use a
   non-character as a pseudo short option, starting with CHAR_MAX + 1.  */
enum
{
  CHECK_OPTION = CHAR_MAX + 1,
  COMPRESS_PROGRAM_OPTION,
  DEBUG_PROGRAM_OPTION,
  FILES0_FROM_OPTION,
  NMERGE_OPTION,
  RANDOM_SOURCE_OPTION,
  SORT_OPTION,
  PARALLEL_OPTION
};

static char const short_options[] = "-bcCdfghik:mMno:rRsS:t:T:uVy:z";

static struct option const long_options[] =
{
  {"ignore-leading-blanks", no_argument, nullptr, 'b'},
  {"check", optional_argument, nullptr, CHECK_OPTION},
  {"compress-program", required_argument, nullptr, COMPRESS_PROGRAM_OPTION},
  {"debug", no_argument, nullptr, DEBUG_PROGRAM_OPTION},
  {"dictionary-order", no_argument, nullptr, 'd'},
  {"ignore-case", no_argument, nullptr, 'f'},
  {"files0-from", required_argument, nullptr, FILES0_FROM_OPTION},
  {"general-numeric-sort", no_argument, nullptr, 'g'},
  {"ignore-nonprinting", no_argument, nullptr, 'i'},
  {"key", required_argument, nullptr, 'k'},
  {"merge", no_argument, nullptr, 'm'},
  {"month-sort", no_argument, nullptr, 'M'},
  {"numeric-sort", no_argument, nullptr, 'n'},
  {"human-numeric-sort", no_argument, nullptr, 'h'},
  {"version-sort", no_argument, nullptr, 'V'},
  {"random-sort", no_argument, nullptr, 'R'},
  {"random-source", required_argument, nullptr, RANDOM_SOURCE_OPTION},
  {"sort", required_argument, nullptr, SORT_OPTION},
  {"output", required_argument, nullptr, 'o'},
  {"reverse", no_argument, nullptr, 'r'},
  {"stable", no_argument, nullptr, 's'},
  {"batch-size", required_argument, nullptr, NMERGE_OPTION},
  {"buffer-size", required_argument, nullptr, 'S'},
  {"field-separator", required_argument, nullptr, 't'},
  {"temporary-directory", required_argument, nullptr, 'T'},
  {"unique", no_argument, nullptr, 'u'},
  {"zero-terminated", no_argument, nullptr, 'z'},
  {"parallel", required_argument, nullptr, PARALLEL_OPTION},
  {GETOPT_HELP_OPTION_DECL},
  {GETOPT_VERSION_OPTION_DECL},
  {nullptr, 0, nullptr, 0},
};

#define CHECK_TABLE \
  _ct_("quiet",          'C') \
  _ct_("silent",         'C') \
  _ct_("diagnose-first", 'c')

static char const *const check_args[] =
{
#define _ct_(_s, _c) _s,
  CHECK_TABLE nullptr
#undef  _ct_
};
static char const check_types[] =
{
#define _ct_(_s, _c) _c,
  CHECK_TABLE
#undef  _ct_
};

#define SORT_TABLE \
  _st_("general-numeric", 'g') \
  _st_("human-numeric",   'h') \
  _st_("month",           'M') \
  _st_("numeric",         'n') \
  _st_("random",          'R') \
  _st_("version",         'V')

static char const *const sort_args[] =
{
#define _st_(_s, _c) _s,
  SORT_TABLE nullptr
#undef  _st_
};
static char const sort_types[] =
{
#define _st_(_s, _c) _c,
  SORT_TABLE
#undef  _st_
};

/* The set of signals that are caught.  */
static sigset_t caught_signals;

/* Critical section status.  */
struct cs_status
{
  bool valid;
  sigset_t sigs;
};

/* Enter a critical section.  */
static void
cs_enter (struct cs_status *status)
{
  if (status == NULL)
  {
    return;
  }

  status->valid = (pthread_sigmask (SIG_BLOCK, &caught_signals, &status->sigs) == 0);
}

/* Leave a critical section.  */
static void
cs_leave (struct cs_status const *status)
{
  if (status && status->valid)
    {
      (void) pthread_sigmask (SIG_SETMASK, &status->sigs, NULL);
    }
}

/* Possible states for a temp file.  If compressed, the file's status
   is unreaped or reaped, depending on whether 'sort' has waited for
   the subprocess to finish.  */
enum { UNCOMPRESSED, UNREAPED, REAPED };

/* The list of temporary files. */
struct tempnode
{
  struct tempnode *volatile next;
  pid_t pid;     /* The subprocess PID; undefined if state == UNCOMPRESSED.  */
  char state;
  char name[FLEXIBLE_ARRAY_MEMBER];
};
static struct tempnode *volatile temphead;
static struct tempnode *volatile *temptail = &temphead;

/* A file to be sorted.  */
struct sortfile
{
  /* The file's name.  */
  char const *name;

  /* Non-null if this is a temporary file, in which case NAME == TEMP->name.  */
  struct tempnode *temp;
};

/* Map PIDs of unreaped subprocesses to their struct tempnode objects.  */
static Hash_table *proctab;

enum { INIT_PROCTAB_SIZE = 47 };

static size_t
proctab_hasher (void const *entry, size_t tabsize)
{
  if (tabsize == 0 || entry == NULL)
  {
    return 0;
  }

  struct tempnode const *node = entry;
  return (size_t)node->pid % tabsize;
}

static bool
proctab_comparator (void const *e1, void const *e2)
{
  if (!e1 || !e2)
    {
      return e1 == e2;
    }

  struct tempnode const *n1 = e1;
  struct tempnode const *n2 = e2;

  return n1->pid == n2->pid;
}

/* The number of unreaped child processes.  */
static pid_t nprocs;

static bool delete_proc (pid_t);

/* If PID is positive, wait for the child process with that PID to
   exit, and assume that PID has already been removed from the process
   table.  If PID is 0 or -1, clean up some child that has exited (by
   waiting for it, and removing it from the proc table) and return the
   child's process ID.  However, if PID is 0 and no children have
   exited, return 0 without waiting.  */

static pid_t
reap (pid_t pid)
{
  int status = 0;
  pid_t const wait_target = (pid != 0) ? pid : -1;
  int const wait_options = (pid != 0) ? 0 : WNOHANG;

  pid_t cpid = waitpid (wait_target, &status, wait_options);

  if (cpid < 0)
    {
      error (SORT_FAILURE, errno, _("waiting for %s [-d]"),
             quoteaf (compress_program));
    }
  else if (cpid > 0)
    {
      bool const should_process = (pid != 0) || delete_proc (cpid);
      if (should_process)
        {
          if (!WIFEXITED (status) || WEXITSTATUS (status) != 0)
            {
              error (SORT_FAILURE, 0, _("%s [-d] terminated abnormally"),
                     quoteaf (compress_program));
            }
          --nprocs;
        }
    }

  return cpid;
}

/* TEMP represents a new process; add it to the process table.  Create
   the process table the first time it's called.  */

static void
ensure_proctab_initialized (void)
{
  if (proctab)
    return;

  proctab = hash_initialize (INIT_PROCTAB_SIZE, NULL,
                             proctab_hasher,
                             proctab_comparator,
                             NULL);
  if (!proctab)
    xalloc_die ();
}

static void
register_proc (struct tempnode *temp)
{
  ensure_proctab_initialized ();

  temp->state = UNREAPED;

  if (!hash_insert (proctab, temp))
    xalloc_die ();
}

/* If PID is in the process table, remove it and return true.
   Otherwise, return false.  */

static bool
delete_proc (pid_t pid)
{
  struct tempnode test = { .pid = pid };
  struct tempnode *node = hash_remove (proctab, &test);

  if (node)
    {
      node->state = REAPED;
    }

  return node != NULL;
}

/* Remove PID from the process table, and wait for it to exit if it
   hasn't already.  */

static void wait_proc(pid_t pid)
{
    if (delete_proc(pid))
    {
        if (reap(pid) != 0)
        {
            /* An error occurred while reaping the process. In a void function
             * without a logging framework, the most robust action is to
             * terminate the function's execution to prevent further issues. */
            return;
        }
    }
}

/* Reap any exited children.  Do not block; reap only those that have
   already exited.  */

static void
reap_exited (void)
{
  while (nprocs > 0 && reap (0))
  {
    /* The loop's work is done in its condition. */
  }
}

/* Reap at least one exited child, waiting if necessary.  */

static void
reap_some (void)
{
  (void) reap (-1);
  reap_exited ();
}

/* Reap all children, waiting if necessary.  */

static void
reap_all(void)
{
    while (nprocs > 0) {
        reap(-1);
    }
}

/* Clean up any remaining temporary files.  */

static void
cleanup (void)
{
  while (temphead)
    {
      struct tempnode *current = temphead;
      temphead = current->next;

      (void) unlink (current->name);
      free (current);
    }
}

/* Cleanup actions to take when exiting.  */

static void
cleanup_in_critical_section(void)
{
    struct cs_status cs;
    cs_enter(&cs);
    cleanup();
    cs_leave(&cs);
}

static void
exit_cleanup(void)
{
    if (temphead)
    {
        cleanup_in_critical_section();
    }

    close_stdout();
}

/* Create a new temporary file, returning its newly allocated tempnode.
   Store into *PFD the file descriptor open for writing.
   If the creation fails, return nullptr and store -1 into *PFD if the
   failure is due to file descriptor exhaustion and
   SURVIVE_FD_EXHAUSTION; otherwise, die.  */

static struct tempnode *
create_temp_file (int *pfd, bool survive_fd_exhaustion)
{
  static char const slashbase[] = "/sortXXXXXX";
  static idx_t temp_dir_index;

  char const *temp_dir = temp_dirs[temp_dir_index];
  temp_dir_index = (temp_dir_index + 1) % temp_dir_count;

  size_t temp_dir_len = strlen (temp_dir);
  struct tempnode *node =
    xmalloc (FLEXSIZEOF (struct tempnode, name, temp_dir_len + sizeof slashbase));
  node->next = NULL;
  sprintf (node->name, "%s%s", temp_dir, slashbase);

  struct cs_status cs;
  int fd;
  int saved_errno;

  cs_enter (&cs);
  fd = mkostemp (node->name, O_CLOEXEC);
  saved_errno = errno;
  if (fd >= 0)
    {
      *temptail = node;
      temptail = &node->next;
    }
  cs_leave (&cs);
  errno = saved_errno;

  if (fd < 0)
    {
      if (! (survive_fd_exhaustion && errno == EMFILE))
        error (SORT_FAILURE, errno, _("cannot create temporary file in %s"),
               quoteaf (temp_dir));
      free (node);
      node = NULL;
    }

  *pfd = fd;
  return node;
}

/* Return a pointer to stdout status, or nullptr on failure.  */

static struct stat *
get_outstatus (void)
{
  static struct stat outstat;
  static bool is_initialized = false;
  static bool success = false;

  if (!is_initialized)
    {
      is_initialized = true;
      success = (fstat (STDOUT_FILENO, &outstat) == 0);
    }

  return success ? &outstat : NULL;
}

/* Return a stream for FILE, opened with mode HOW.  If HOW is "w",
   the file is already open on standard output, and needs to be
   truncated unless FILE is null.  When opening for input, "-"
   means standard input.  To avoid confusion, do not return file
   descriptors STDIN_FILENO, STDOUT_FILENO, or STDERR_FILENO when
   opening an ordinary FILE.  Return nullptr if unsuccessful.

   Use fadvise to specify an access pattern for input files.
   There are a few hints we could possibly provide,
   and after careful testing it was decided that
   specifying FADVISE_SEQUENTIAL was not detrimental
   to any cases.  On Linux 2.6.31, this option doubles
   the size of read ahead performed and thus was seen to
   benefit these cases:
     Merging
     Sorting with a smaller internal buffer
     Reading from faster flash devices

   In _addition_ one could also specify other hints...

   FADVISE_WILLNEED was tested, but Linux 2.6.31
   at least uses that to _synchronously_ prepopulate the cache
   with the specified range.  While sort does need to
   read all of its input before outputting, a synchronous
   read of the whole file up front precludes any processing
   that sort could do in parallel with the system doing
   read ahead of the data. This was seen to have negative effects
   in a couple of cases:
     Merging
     Sorting with a smaller internal buffer
   This option was seen to shorten the runtime for sort
   on a multicore system with lots of RAM and other processes
   competing for CPU.  It could be argued that more explicit
   scheduling hints with 'nice' et. al. are more appropriate
   for this situation.

   FADVISE_NOREUSE is a possibility as it could lower
   the priority of input data in the cache as sort will
   only need to process it once.  However its functionality
   has changed over Linux kernel versions and as of 2.6.31
   it does nothing and thus we can't depend on what it might
   do in future.

   FADVISE_DONTNEED is not appropriate for user specified
   input files, but for temp files we do want to drop the
   cache immediately after processing.  This is done implicitly
   however when the files are unlinked.  */

static FILE *
stream_open (char const *file, char const *how)
{
  FILE *fp = NULL;

  if (*how == 'r')
    {
      if (STREQ (file, "-"))
        {
          have_read_stdin = true;
          fp = stdin;
        }
      else
        {
          int fd = open (file, O_RDONLY | O_CLOEXEC);
          if (fd >= 0)
            {
              fp = fdopen (fd, how);
              if (!fp)
                {
                  close (fd);
                }
            }
        }

      if (fp)
        {
          fadvise (fp, FADVISE_SEQUENTIAL);
        }
    }
  else if (*how == 'w')
    {
      if (file)
        {
          if (ftruncate (STDOUT_FILENO, 0) != 0)
            {
              int ftruncate_errno = errno;
              struct stat *outst = get_outstatus ();
              bool is_truncatable_type = (!outst || S_ISREG (outst->st_mode)
                                          || S_TYPEISSHM (outst));
              if (is_truncatable_type)
                {
                  error (SORT_FAILURE, ftruncate_errno,
                         _("%s: error truncating"), quotef (file));
                }
            }
        }
      fp = stdout;
    }
  else
    {
      affirm (!"unexpected mode passed to stream_open");
    }

  return fp;
}

/* Same as stream_open, except always return a non-null value; die on
   failure.  */

static FILE *
xfopen (char const *file, char const *how)
{
  FILE * const fp = stream_open (file, how);
  if (fp == NULL)
  {
    /* sort_die is expected to terminate the program and not return. */
    sort_die (_("open failed"), file);
  }
  return fp;
}

/* Close FP, whose name is FILE, and report any errors.  */

static void
xfclose (FILE *fp, char const *file)
{
  if (!fp)
    {
      return;
    }

  if (fp == stdin)
    {
      clearerr (fp);
    }
  else if (fp == stdout)
    {
      if (fflush (fp) != 0)
        {
          sort_die (_("fflush failed"), file);
        }
    }
  else
    {
      if (fclose (fp) != 0)
        {
          sort_die (_("close failed"), file);
        }
    }
}

/* Move OLDFD to NEWFD.  If OLDFD != NEWFD, NEWFD is not close-on-exec.  */

static void
move_fd (int oldfd, int newfd)
{
  if (oldfd == newfd)
    {
      return;
    }

  if (dup2 (oldfd, newfd) == -1)
    {
      perror ("dup2 failed");
      exit (EXIT_FAILURE);
    }

  if (close (oldfd) == -1)
    {
      perror ("close failed");
      exit (EXIT_FAILURE);
    }
}

/* Fork a child process for piping to and do common cleanup.  The
   TRIES parameter specifies how many times to try to fork before
   giving up.  Return the PID of the child, or -1 (setting errno)
   on failure. */

static pid_t
pipe_fork (int pipefds[2], size_t tries)
{
#if HAVE_WORKING_FORK
  if (pipe2 (pipefds, O_CLOEXEC) < 0)
    {
      return -1;
    }

  if (nmerge + 1 < nprocs)
    {
      reap_some ();
    }

  pid_t pid = -1;
  double wait_retry = 0.25;

  while (tries--)
    {
      struct cs_status cs;
      struct tempnode *saved_temphead;
      int fork_errno;

      cs_enter (&cs);
      saved_temphead = temphead;
      temphead = NULL;

      pid = fork ();
      fork_errno = errno;

      if (pid != 0)
        {
          temphead = saved_temphead;
        }

      cs_leave (&cs);
      errno = fork_errno;

      if (pid >= 0)
        {
          break;
        }

      if (errno != EAGAIN)
        {
          break;
        }

      xnanosleep (wait_retry);
      wait_retry *= 2;
      reap_exited ();
    }

  if (pid < 0)
    {
      int saved_errno = errno;
      close (pipefds[0]);
      close (pipefds[1]);
      errno = saved_errno;
      return -1;
    }

  if (pid == 0)
    {
      close (STDIN_FILENO);
      close (STDOUT_FILENO);
    }
  else
    {
      ++nprocs;
    }

  return pid;

#else  /* ! HAVE_WORKING_FORK */
  return -1;
#endif
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return
   the address of the new temp node.  If the creation
   fails, return nullptr if the failure is due to file descriptor
   exhaustion and SURVIVE_FD_EXHAUSTION; otherwise, die.  */

static void
compress_child_process (int tempfd, int pipe_read_fd)
{
  move_fd (tempfd, STDOUT_FILENO);
  move_fd (pipe_read_fd, STDIN_FILENO);
  execlp (compress_program, compress_program, (char *) NULL);
  async_safe_die (errno, "couldn't execute compress program");
}

static int
start_compressor (struct tempnode *node, int old_tempfd)
{
  int pipefds[2];

  node->pid = pipe_fork (pipefds, MAX_FORK_TRIES_COMPRESS);

  if (node->pid < 0)
    {
      close (old_tempfd);
      sort_die (_("couldn't create process for compression"), node->name);
    }

  if (node->pid == 0)
    {
      close (pipefds[1]);
      compress_child_process (old_tempfd, pipefds[0]);
    }

  close (old_tempfd);
  close (pipefds[0]);
  register_proc (node);
  return pipefds[1];
}

static struct tempnode *
maybe_create_temp (FILE **pfp, bool survive_fd_exhaustion)
{
  int tempfd;
  struct tempnode *node = create_temp_file (&tempfd, survive_fd_exhaustion);
  if (!node)
    return NULL;

  node->state = UNCOMPRESSED;

  if (compress_program)
    tempfd = start_compressor (node, tempfd);

  *pfp = fdopen (tempfd, "w");
  if (!*pfp)
    {
      int saved_errno = errno;
      close (tempfd);
      errno = saved_errno;
      sort_die (_("couldn't create temporary file"), node->name);
    }

  return node;
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return the address
   of the new temp node.  Die on failure.  */

static struct tempnode *
create_temp (FILE **pfp)
{
  if (!pfp)
    {
      return NULL;
    }
  return maybe_create_temp (pfp, false);
}

/* Open a compressed temp file and start a decompression process through
   which to filter the input.  Return nullptr (setting errno to
   EMFILE) if we ran out of file descriptors, and die on any other
   kind of failure.  */

static FILE *
open_temp (struct tempnode *temp)
{
  if (temp->state == UNREAPED)
    {
      wait_proc (temp->pid);
    }

  int tempfd = open (temp->name, O_RDONLY);
  if (tempfd < 0)
    {
      return NULL;
    }

  int pipefds[2];
  pid_t child = pipe_fork (pipefds, MAX_FORK_TRIES_DECOMPRESS);

  if (child < 0)
    {
      if (errno != EMFILE)
        {
          error (SORT_FAILURE, errno, _("couldn't create process for %s -d"),
                 quoteaf (compress_program));
        }
      close (tempfd);
      errno = EMFILE;
      return NULL;
    }

  if (child == 0)
    {
      close (pipefds[0]);
      move_fd (tempfd, STDIN_FILENO);
      move_fd (pipefds[1], STDOUT_FILENO);

      execlp (compress_program, compress_program, "-d", (char *) NULL);

      async_safe_die (errno, "couldn't execute compress program (with -d)");
    }

  close (tempfd);
  close (pipefds[1]);

  FILE *fp = fdopen (pipefds[0], "r");
  if (!fp)
    {
      int saved_errno = errno;
      close (pipefds[0]);
      errno = saved_errno;
      return NULL;
    }

  temp->pid = child;
  register_proc (temp);
  return fp;
}

/* Append DIR to the array of temporary directory names.  */
static void
add_temp_dir (char const *dir)
{
  if (!dir)
    {
      return;
    }

  if (temp_dir_count == temp_dir_alloc)
    {
      temp_dirs = xpalloc (temp_dirs, &temp_dir_alloc, 1, -1, sizeof *temp_dirs);
    }

  temp_dirs[temp_dir_count++] = dir;
}

/* Remove NAME from the list of temporary files.  */

static void
zaptemp (char const *name)
{
  struct tempnode *volatile *pnode = &temphead;
  struct tempnode *node;

  while (*pnode && (*pnode)->name != name)
  {
    pnode = &(*pnode)->next;
  }

  node = *pnode;
  if (!node)
  {
    return;
  }

  if (node->state == UNREAPED)
  {
    wait_proc (node->pid);
  }

  struct tempnode *next = node->next;
  int unlink_status;
  int unlink_errno;
  struct cs_status cs;

  cs_enter (&cs);
  unlink_status = unlink (name);
  unlink_errno = errno;
  *pnode = next;
  cs_leave (&cs);

  if (unlink_status != 0)
  {
    error (0, unlink_errno, _("warning: cannot remove: %s"), quotef (name));
  }

  if (!next)
  {
    temptail = pnode;
  }

  free (node);
}

#if HAVE_NL_LANGINFO

static int
struct_month_cmp (void const *m1, void const *m2)
{
  struct month const *month1 = m1;
  struct month const *month2 = m2;
  return strcmp (month1->name, month2->name);
}

#endif

/* Initialize the character class tables. */

static void
inittables (void)
{
  for (size_t i = 0; i < UCHAR_LIM; ++i)
    {
      const int is_a_blank = (i == '\n' || isblank (i));
      blanks[i] = is_a_blank;
      nondictionary[i] = !is_a_blank && !isalnum (i);
      nonprinting[i] = !isprint (i);
      fold_toupper[i] = toupper ((unsigned char) i);
    }

#if HAVE_NL_LANGINFO
  if (hard_LC_TIME)
    {
      for (size_t i = 0; i < MONTHS_PER_YEAR; i++)
        {
          const char *s = nl_langinfo (ABMON_1 + i);
          const size_t s_len = strlen (s);
          char *name = xmalloc (s_len + 1);

          monthtab[i].name = name;
          monthtab[i].val = i + 1;

          char *dest = name;
          for (size_t j = 0; j < s_len; j++)
            {
              const unsigned char c = to_uchar (s[j]);
              if (!isblank (c))
                {
                  *dest++ = fold_toupper[c];
                }
            }
          *dest = '\0';
        }
      qsort (monthtab, MONTHS_PER_YEAR, sizeof *monthtab, struct_month_cmp);
    }
#endif
}

/* Specify how many inputs may be merged at once.
   This may be set on the command-line with the
   --batch-size option. */
static void
specify_nmerge (int oi, char c, char const *s)
{
  uintmax_t n;
  enum strtol_error e = xstrtoumax (s, nullptr, 10, &n, "");

  rlim_t limit;
  struct rlimit rlimit_value;
  if (getrlimit (RLIMIT_NOFILE, &rlimit_value) == 0)
    limit = rlimit_value.rlim_cur;
  else
    limit = OPEN_MAX;

  unsigned int max_nmerge = (limit > 3 ? limit - 3 : 0);

  if (e == LONGINT_OK)
    {
      if (n < 2)
        {
          error (0, 0, _("invalid --%s argument %s"),
                 long_options[oi].name, quote (s));
          error (SORT_FAILURE, 0,
                 _("minimum --%s argument is %s"),
                 long_options[oi].name, quote ("2"));
        }

      if (n <= max_nmerge)
        {
          nmerge = n;
          return;
        }

      e = LONGINT_OVERFLOW;
    }

  if (e == LONGINT_OVERFLOW)
    {
      error (0, 0, _("--%s argument %s too large"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("maximum --%s argument with current rlimit is %u"),
             long_options[oi].name, max_nmerge);
    }
  else
    {
      xstrtol_fatal (e, oi, c, long_options, s);
    }
}

/* Specify the amount of main memory to use when sorting.  */
static void
specify_sort_size (int oi, char c, char const *s)
{
  uintmax_t n;
  char *suffix;
  enum strtol_error e = xstrtoumax (s, &suffix, 10, &n, "EgGkKmMPQRtTYZ");

  if (e == LONGINT_INVALID_SUFFIX_CHAR && c_isdigit (suffix[-1]) && !suffix[1])
    {
      switch (suffix[0])
        {
        case 'b':
          e = LONGINT_OK;
          break;
        case '%':
          {
            double mem_bytes = physmem_total () * ((double) n / 100.0);
            if (mem_bytes < (double) UINTMAX_MAX)
              {
                n = (uintmax_t) mem_bytes;
                e = LONGINT_OK;
              }
            else
              {
                e = LONGINT_OVERFLOW;
              }
          }
          break;
        }
    }
  else if (e == LONGINT_OK && c_isdigit (suffix[-1]))
    {
      if (n > UINTMAX_MAX / 1024)
        e = LONGINT_OVERFLOW;
      else
        n *= 1024;
    }

  if (e != LONGINT_OK)
    {
      xstrtol_fatal (e, oi, c, long_options, s);
    }

  if (n <= sort_size)
    {
      return;
    }

  sort_size = n;
  if (sort_size != n)
    {
      xstrtol_fatal (LONGINT_OVERFLOW, oi, c, long_options, s);
    }

  sort_size = MAX (sort_size, MIN_SORT_SIZE);
}

/* Specify the number of threads to spawn during internal sort.  */
static size_t
specify_nthreads (int oi, char c, char const *s)
{
  uintmax_t nthreads;
  enum strtol_error e = xstrtoumax (s, NULL, 10, &nthreads, "");

  if (e != LONGINT_OK && e != LONGINT_OVERFLOW)
    xstrtol_fatal (e, oi, c, long_options, s);

  if (nthreads == 0)
    error (SORT_FAILURE, 0, _("number in parallel must be nonzero"));

  if (nthreads > SIZE_MAX)
    return SIZE_MAX;

  return (size_t) nthreads;
}

/* Return the default sort size.  */
static size_t
default_sort_size(void)
{
    struct rlimit rlimit;
    size_t size_limit = SIZE_MAX;

    if (getrlimit(RLIMIT_DATA, &rlimit) == 0 && rlimit.rlim_cur < size_limit) {
        size_limit = rlimit.rlim_cur;
    }
#ifdef RLIMIT_AS
    if (getrlimit(RLIMIT_AS, &rlimit) == 0 && rlimit.rlim_cur < size_limit) {
        size_limit = rlimit.rlim_cur;
    }
#endif

    const int resource_limit_safety_divisor = 2;
    size_limit /= resource_limit_safety_divisor;

#ifdef RLIMIT_RSS
    if (getrlimit(RLIMIT_RSS, &rlimit) == 0) {
        const int rss_margin_numerator = 15;
        const int rss_margin_denominator = 16;
        size_t rss_limit = (rlimit.rlim_cur / rss_margin_denominator)
                           * rss_margin_numerator;
        if (rss_limit < size_limit) {
            size_limit = rss_limit;
        }
    }
#endif

    double total_mem = physmem_total();
    const double physical_mem_safety_factor = 0.75;
    size_t phys_mem_cap = (size_t)(total_mem * physical_mem_safety_factor);
    if (phys_mem_cap < size_limit) {
        size_limit = phys_mem_cap;
    }

    const double total_mem_fraction_denominator = 8.0;
    double available_mem = physmem_available();
    double target_mem =
        MAX(available_mem, total_mem / total_mem_fraction_denominator);

    if (target_mem < size_limit) {
        size_limit = (size_t)target_mem;
    }

    return MAX(size_limit, MIN_SORT_SIZE);
}

/* Return the sort buffer size to use with the input files identified
   by FPS and FILES, which are alternate names of the same files.
   NFILES gives the number of input files; NFPS may be less.  Assume
   that each input line requires LINE_BYTES extra bytes' worth of line
   information.  Do not exceed the size bound specified by the user
   (or a default size bound, if the user does not specify one).  */

static size_t
sort_buffer_size (FILE *const *fps, size_t nfps,
                  char *const *files, size_t nfiles,
                  size_t line_bytes)
{
  const size_t size_bound = sort_size ? sort_size : default_sort_size();
  const size_t worst_case_per_input_byte = line_bytes + 1;

  size_t total_size = worst_case_per_input_byte + 1;

  for (size_t i = 0; i < nfiles; i++)
    {
      struct stat st;
      int stat_result;

      if (i < nfps)
        stat_result = fstat(fileno(fps[i]), &st);
      else if (STREQ(files[i], "-"))
        stat_result = fstat(STDIN_FILENO, &st);
      else
        stat_result = stat(files[i], &st);

      if (stat_result != 0)
        sort_die(_("stat failed"), files[i]);

      off_t file_size;
      if (usable_st_size(&st) && st.st_size > 0)
        {
          file_size = st.st_size;
        }
      else
        {
          if (sort_size)
            return sort_size;
          file_size = INPUT_FILE_SIZE_GUESS;
        }

      if (worst_case_per_input_byte > 0 &&
          (size_t)file_size > (SIZE_MAX - 1) / worst_case_per_input_byte)
        return size_bound;

      size_t required_mem_for_file = (size_t)file_size * worst_case_per_input_byte + 1;

      if (size_bound - total_size <= required_mem_for_file)
        return size_bound;

      total_size += required_mem_for_file;
    }

  return total_size;
}

/* Initialize BUF.  Reserve LINE_BYTES bytes for each line; LINE_BYTES
   must be at least sizeof (struct line).  Allocate ALLOC bytes
   initially.  */

static void
initbuf (struct buffer *buf, size_t line_bytes, size_t alloc)
{
  const size_t min_alloc_threshold = line_bytes + 1;
  const size_t line_size = sizeof (struct line);

  while (true)
    {
      size_t size_to_alloc = alloc;
      size_t remainder = alloc % line_size;

      if (remainder != 0)
        {
          size_to_alloc += line_size - remainder;
        }

      if (size_to_alloc >= alloc)
        {
          buf->buf = malloc (size_to_alloc);
          if (buf->buf)
            {
              buf->alloc = size_to_alloc;
              break;
            }
        }

      alloc /= 2;
      if (alloc <= min_alloc_threshold)
        {
          xalloc_die ();
        }
    }

  buf->line_bytes = line_bytes;
  buf->used = 0;
  buf->left = 0;
  buf->nlines = 0;
  buf->eof = false;
}

/* Return one past the limit of the line array.  */

static inline struct line *
buffer_linelim (struct buffer const *buf)
{
  return (struct line *) ((char *) buf->buf + buf->alloc);
}

/* Return a pointer to the first character of the field specified
   by KEY in LINE. */

static char *
begfield (struct line const *line, struct keyfield const *key)
{
  if (line->length == 0)
    return line->text;

  char *ptr = line->text;
  char *lim = ptr + line->length - 1;
  size_t sword = key->sword;

  if (tab != TAB_DEFAULT)
    {
      while (sword-- > 0 && ptr < lim)
        {
          char *next_tab = memchr (ptr, tab, lim - ptr);
          ptr = next_tab ? next_tab + 1 : lim;
        }
    }
  else
    {
      while (sword-- > 0 && ptr < lim)
        {
          while (ptr < lim && blanks[to_uchar (*ptr)])
            ++ptr;
          while (ptr < lim && !blanks[to_uchar (*ptr)])
            ++ptr;
        }
    }

  if (key->skipsblanks)
    {
      while (ptr < lim && blanks[to_uchar (*ptr)])
        ++ptr;
    }

  size_t schar = key->schar;
  size_t remaining_bytes = lim - ptr;
  ptr += (schar < remaining_bytes) ? schar : remaining_bytes;

  return ptr;
}

/* Return the limit of (a pointer to the first character after) the field
   in LINE specified by KEY. */

static void
skip_tab_delimited_fields (char **ptr_p, char *lim, size_t n, size_t echar,
                           char tab)
{
  char *ptr = *ptr_p;
  while (n > 0 && ptr < lim)
    {
      char *next_tab = memchr (ptr, tab, lim - ptr);
      if (next_tab == NULL)
        {
          ptr = lim;
          break;
        }
      ptr = next_tab;
      if (n > 1 || echar != 0)
        {
          if (ptr < lim)
            {
              ++ptr;
            }
        }
      --n;
    }
  *ptr_p = ptr;
}

static void
skip_blank_delimited_fields (char **ptr_p, char *lim, size_t n)
{
  char *ptr = *ptr_p;
  while (n > 0 && ptr < lim)
    {
      while (ptr < lim && blanks[to_uchar (*ptr)])
        {
          ++ptr;
        }
      if (ptr < lim)
        {
          while (ptr < lim && !blanks[to_uchar (*ptr)])
            {
              ++ptr;
            }
        }
      --n;
    }
  *ptr_p = ptr;
}

#ifdef POSIX_UNSPECIFIED
static char *
find_field_end (char *ptr, char *lim)
{
  if (tab != TAB_DEFAULT)
    {
      char *field_end = memchr (ptr, tab, lim - ptr);
      return field_end ? field_end : lim;
    }
  else
    {
      char *p = ptr;
      while (p < lim && blanks[to_uchar (*p)])
        ++p;
      while (p < lim && !blanks[to_uchar (*p)])
        ++p;
      return p;
    }
}
#endif

ATTRIBUTE_PURE
static char *
limfield (struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text;
  char *lim = ptr + line->length;
  size_t eword = key->eword;
  size_t echar = key->echar;

  if (echar == 0)
    {
      eword++;
    }

  if (tab != TAB_DEFAULT)
    {
      skip_tab_delimited_fields (&ptr, lim, eword, echar, tab);
    }
  else
    {
      skip_blank_delimited_fields (&ptr, lim, eword);
    }

#ifdef POSIX_UNSPECIFIED
  lim = find_field_end (ptr, lim);
#endif

  if (echar != 0)
    {
      if (key->skipeblanks)
        {
          while (ptr < lim && blanks[to_uchar (*ptr)])
            {
              ++ptr;
            }
        }

      size_t remaining_bytes = lim - ptr;
      ptr = (echar < remaining_bytes) ? ptr + echar : lim;
    }

  return ptr;
}

/* Fill BUF reading from FP, moving buf->left bytes from the end
   of buf->buf to the beginning first.  If EOF is reached and the
   file wasn't terminated by a newline, supply one.  Set up BUF's line
   table too.  FILE is the name of the file corresponding to FP.
   Return true if some input was read.  */

static void
set_key_fields (struct line *line, struct keyfield const *key,
                char *line_start, char *line_end)
{
  line->keylim = (key->eword == SIZE_MAX ? line_end : limfield (line, key));

  if (key->sword != SIZE_MAX)
    {
      line->keybeg = begfield (line, key);
    }
  else
    {
      if (key->skipsblanks)
        while (blanks[to_uchar (*line_start)])
          line_start++;
      line->keybeg = line_start;
    }
}

static bool
fillbuf (struct buffer *buf, FILE *fp, char const *file)
{
  struct keyfield const *key = keylist;
  char eol = eolchar;
  size_t mergesize = merge_buffer_size - MIN_MERGE_BUFFER_SIZE;

  if (buf->eof)
    return false;

  if (buf->used > buf->left)
    {
      memmove (buf->buf, buf->buf + buf->used - buf->left, buf->left);
      buf->used = buf->left;
      buf->nlines = 0;
    }

  while (true)
    {
      char *text_write_ptr = buf->buf + buf->used;
      struct line *line_desc_limit = buffer_linelim (buf);
      struct line *line_desc_ptr = line_desc_limit - buf->nlines;
      size_t const line_desc_bytes = buf->line_bytes;

      char *current_line_start = buf->nlines
                                 ? line_desc_ptr->text + line_desc_ptr->length
                                 : buf->buf;

      size_t avail_text_space = (char *) line_desc_limit
                              - (buf->nlines * line_desc_bytes)
                              - text_write_ptr;

      while (line_desc_bytes + 1 < avail_text_space)
        {
          size_t const worst_case_byte_cost = line_desc_bytes + 1;
          size_t readsize = (avail_text_space - 1) / worst_case_byte_cost;
          size_t bytes_read = fread (text_write_ptr, 1, readsize, fp);
          char *read_end_ptr = text_write_ptr + bytes_read;
          avail_text_space -= bytes_read;

          if (bytes_read < readsize)
            {
              if (ferror (fp))
                sort_die (_("read failed"), file);

              if (feof (fp))
                {
                  buf->eof = true;
                  if (buf->buf == read_end_ptr)
                    return false;
                  if (current_line_start < read_end_ptr && read_end_ptr[-1] != eol)
                    *read_end_ptr++ = eol;
                }
            }

          char *eol_ptr;
          while ((eol_ptr = memchr (text_write_ptr, eol, read_end_ptr - text_write_ptr)))
            {
              *eol_ptr = '\0';
              text_write_ptr = eol_ptr + 1;

              line_desc_ptr--;
              line_desc_ptr->text = current_line_start;
              line_desc_ptr->length = text_write_ptr - current_line_start;
              mergesize = MAX (mergesize, line_desc_ptr->length);
              avail_text_space -= line_desc_bytes;

              if (key)
                set_key_fields (line_desc_ptr, key, current_line_start, eol_ptr);

              current_line_start = text_write_ptr;
            }

          text_write_ptr = read_end_ptr;
          if (buf->eof)
            break;
        }

      buf->used = text_write_ptr - buf->buf;
      buf->nlines = line_desc_limit - line_desc_ptr;
      if (buf->nlines > 0)
        {
          buf->left = text_write_ptr - current_line_start;
          merge_buffer_size = mergesize + MIN_MERGE_BUFFER_SIZE;
          return true;
        }

      if (buf->eof)
        return false;

      idx_t line_alloc = buf->alloc / sizeof (struct line);
      buf->buf = xpalloc (buf->buf, &line_alloc, 1, -1, sizeof (struct line));
      buf->alloc = line_alloc * sizeof (struct line);
    }
}

/* Table that maps characters to order-of-magnitude values.  */
static char const unit_order[UCHAR_LIM] =
  {
#if ! ('K' == 75 && 'M' == 77 && 'G' == 71 && 'T' == 84 && 'P' == 80 \
       && 'E' == 69 && 'Z' == 90 && 'Y' == 89 && 'R' == 82 && 'Q' == 81 \
       && 'k' == 107)
    /* This initializer syntax works on all C99 hosts.  For now, use
       it only on non-ASCII hosts, to ease the pain of porting to
       pre-C99 ASCII hosts.  */
    ['K']=1, ['M']=2, ['G']=3, ['T']=4, ['P']=5, ['E']=6, ['Z']=7, ['Y']=8,
    ['R']=9, ['Q']=10,
    ['k']=1,
#else
    /* Generate the following table with this command:
       perl -e 'my %a=(k=>1,K=>1,M=>2,G=>3,T=>4,P=>5,E=>6,Z=>7,Y=>8,R=>9,Q=>10);
       foreach my $i (0..255) {my $c=chr($i); $a{$c} ||= 0;print "$a{$c}, "}'\
       |fmt  */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3,
    0, 0, 0, 1, 0, 2, 0, 0, 5, 10, 9, 0, 4, 0, 0, 0, 0, 8, 7, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
#endif
  };

/* Traverse number given as *number consisting of digits, thousands_sep, and
   decimal_point chars only.  Returns the highest digit found in the number,
   or '\0' if no digit has been found.  Upon return *number points at the
   character that immediately follows after the given number.  */
static char
traverse_raw_number (char const **number)
{
  char const *p = *number;
  char max_digit = '\0';

  while (1)
    {
      if (c_isdigit (*p))
        {
          if (max_digit < *p)
            {
              max_digit = *p;
            }
          p++;
        }
      else if (*p == thousands_sep && c_isdigit (p[1]))
        {
          p++;
        }
      else
        {
          break;
        }
    }

  if (*p == decimal_point && c_isdigit (p[1]))
    {
      p++;
      while (c_isdigit (*p))
        {
          if (max_digit < *p)
            {
              max_digit = *p;
            }
          p++;
        }
    }

  *number = p;
  return max_digit;
}

/* Return an integer that represents the order of magnitude of the
   unit following the number.  The number may contain thousands
   separators and a decimal point, but it may not contain leading blanks.
   Negative numbers get negative orders; zero numbers have a zero order.  */

ATTRIBUTE_PURE
static int
find_unit_order (char const *number)
{
    int sign = 1;
    char const *p = number;

    if (*p == '-')
    {
        sign = -1;
        p++;
    }

    char max_digit = traverse_raw_number(&p);
    if (max_digit <= '0')
    {
        return 0;
    }

    unsigned char suffix = *p;
    int order = unit_order[suffix];

    return order * sign;
}

/* Compare numbers A and B ending in units with SI or IEC prefixes
       <none/unknown> < K/k < M < G < T < P < E < Z < Y < R < Q */

ATTRIBUTE_PURE
static int
human_numcompare (char const *a, char const *b)
{
  const char *p_a = a;
  const char *p_b = b;

  while (*p_a && blanks[to_uchar (*p_a)])
    {
      p_a++;
    }
  while (*p_b && blanks[to_uchar (*p_b)])
    {
      p_b++;
    }

  int order_a = find_unit_order (p_a);
  int order_b = find_unit_order (p_b);

  if (order_a != order_b)
    {
      return order_a - order_b;
    }

  return strnumcmp (p_a, p_b, decimal_point, thousands_sep);
}

/* Compare strings A and B as numbers without explicitly converting them to
   machine numbers.  Comparatively slow for short strings, but asymptotically
   hideously fast. */

static char const *
skip_leading_blanks (char const *s)
{
  while (blanks[to_uchar (*s)])
    {
      s++;
    }
  return s;
}

ATTRIBUTE_PURE
static int
numcompare (char const *a, char const *b)
{
  if (a == NULL)
    {
      return (b == NULL) ? 0 : -1;
    }
  if (b == NULL)
    {
      return 1;
    }

  char const *num_a = skip_leading_blanks (a);
  char const *num_b = skip_leading_blanks (b);

  return strnumcmp (num_a, num_b, decimal_point, thousands_sep);
}

static int
nan_compare (long double a, long double b)
{
  if (a > b) {
    return 1;
  }
  if (a < b) {
    return -1;
  }

  int a_is_nan = isnan(a);
  int b_is_nan = isnan(b);

  if (a_is_nan != b_is_nan) {
    return a_is_nan - b_is_nan;
  }

  if (a_is_nan) {
    unsigned char a_bytes[sizeof a];
    unsigned char b_bytes[sizeof b];
    memcpy(a_bytes, &a, sizeof a);
    memcpy(b_bytes, &b, sizeof b);
    return memcmp(a_bytes, b_bytes, sizeof a);
  }

  return signbit(b) - signbit(a);
}

#include <math.h>
#include <stdlib.h>

/* Forward declaration for the comparison function for two NaN values,
   which is assumed to exist elsewhere. */
static int nan_compare (long double a, long double b);

static int
general_numcompare (char const *sa, char const *sb)
{
  char *ea;
  long double a = strtold (sa, &ea);
  int a_is_number = (sa != ea);

  char *eb;
  long double b = strtold (sb, &eb);
  int b_is_number = (sb != eb);

  if (!a_is_number)
    {
      return b_is_number ? -1 : 0;
    }
  if (!b_is_number)
    {
      return 1;
    }

  int a_is_nan = isnan (a);
  int b_is_nan = isnan (b);

  if (a_is_nan)
    {
      return b_is_nan ? nan_compare (a, b) : -1;
    }
  if (b_is_nan)
    {
      return 1;
    }

  if (a < b)
    {
      return -1;
    }
  if (a > b)
    {
      return 1;
    }
  return 0;
}

/* Return an integer in 1..12 of the month name MONTH.
   Return 0 if the name in S is not recognized.  */

static int
getmonth (char const *month, char **ea)
{
  if (!month)
    {
      return 0;
    }

  while (blanks[to_uchar (*month)])
    {
      month++;
    }

  size_t lo = 0;
  size_t hi = MONTHS_PER_YEAR;

  while (lo < hi)
    {
      size_t mid = lo + (hi - lo) / 2;
      char const *m_ptr = month;
      char const *name_ptr = monthtab[mid].name;
      int diff = 0;

      while (*name_ptr)
        {
          unsigned char m_char_upper = fold_toupper[to_uchar (*m_ptr)];
          unsigned char n_char = to_uchar (*name_ptr);

          if (m_char_upper != n_char)
            {
              diff = (m_char_upper > n_char) - (m_char_upper < n_char);
              break;
            }
          m_ptr++;
          name_ptr++;
        }

      if (diff == 0)
        {
          if (ea)
            {
              *ea = (char *) m_ptr;
            }
          return monthtab[mid].val;
        }

      if (diff < 0)
        {
          hi = mid;
        }
      else
        {
          lo = mid + 1;
        }
    }

  return 0;
}

/* When using the OpenSSL implementation, dynamically link only if -R.
   This saves startup time in the usual (sans -R) case.  */

#if DLOPEN_LIBCRYPTO && HAVE_OPENSSL_MD5
/* In the typical case where md5.h does not #undef HAVE_OPENSSL_MD5,
   trick md5.h into declaring and using pointers to functions not functions.
   This causes the compiler's -lcrypto option to have no effect,
   as sort.o no longer uses any crypto symbols statically.  */

# if 14 <= __GNUC__
#  pragma GCC diagnostic push
#  pragma GCC diagnostic ignored "-Wmissing-variable-declarations"
# endif
# define MD5_Init (*ptr_MD5_Init)
# define MD5_Update (*ptr_MD5_Update)
# define MD5_Final (*ptr_MD5_Final)
#endif

#include "md5.h"

#if DLOPEN_LIBCRYPTO && HAVE_OPENSSL_MD5
# if 14 <= __GNUC__
#  pragma GCC diagnostic pop
# endif
# include <dlfcn.h>

/* Diagnose a dynamic linking failure.  */
static void
link_failure (void)
{
  error (SORT_FAILURE, 0, "%s", dlerror ());
}

/* Return a function pointer in HANDLE for SYMBOL.  */
static void *
symbol_address (void *handle, char const *symbol)
{
  void *address = dlsym (handle, symbol);
  if (!address)
    link_failure ();
  return address;
}
#endif

/* Dynamically link the crypto library, if it needs linking.  */
static void
link_libcrypto (void)
{
#if DLOPEN_LIBCRYPTO && HAVE_OPENSSL_MD5
  void *handle = dlopen (LIBCRYPTO_SONAME, RTLD_LAZY | RTLD_GLOBAL);
  if (handle)
    {
      ptr_MD5_Init = symbol_address (handle, "MD5_Init");
      ptr_MD5_Update = symbol_address (handle, "MD5_Update");
      ptr_MD5_Final = symbol_address (handle, "MD5_Final");

      if (ptr_MD5_Init && ptr_MD5_Update && ptr_MD5_Final)
        return;

      dlclose (handle);
    }
  link_failure ();
#endif
}

/* A randomly chosen MD5 state, used for random comparison.  */
static struct md5_ctx random_md5_state;

/* Initialize the randomly chosen MD5 state.  */

static void
random_md5_state_init (char const *random_source)
{
  unsigned char buf[MD5_DIGEST_SIZE];
  char const *source_name = random_source ? random_source : "getrandom";

  struct randread_source *r = randread_new (random_source, sizeof buf);
  if (!r)
    sort_die (_("open failed"), source_name);

  if (randread (r, buf, sizeof buf) != sizeof buf)
    {
      randread_free (r);
      sort_die (_("read failed"), source_name);
    }

  if (randread_free (r) != 0)
    sort_die (_("close failed"), source_name);

  link_libcrypto ();
  md5_init_ctx (&random_md5_state);
  md5_process_bytes (buf, sizeof buf, &random_md5_state);
}

/* This is like strxfrm, except it reports any error and exits.  */

static size_t
xstrxfrm (char *restrict dest, char const *restrict src, size_t destsize)
{
  errno = 0;
  size_t translated_size = strxfrm (dest, src, destsize);

  if (errno)
    {
      error (SORT_FAILURE, errno,
             _("string transformation failed for %s\n"
               "set LC_ALL='C' to work around the problem"),
             quotearg_n_style (0, locale_quoting_style, src));
    }

  return translated_size;
}

/* Compare the keys TEXTA (of length LENA) and TEXTB (of length LENB)
   using one or more random hash functions.  TEXTA[LENA] and
   TEXTB[LENB] must be zero.  */

static int
compute_tiebreaker (const char *a, size_t lena, const char *b, size_t lenb)
{
  int diff = memcmp (a, b, MIN (lena, lenb));
  if (diff == 0)
    {
      diff = _GL_CMP (lena, lenb);
    }
  return diff;
}

static int
compare_random (char *restrict texta, size_t lena,
                char *restrict textb, size_t lenb)
{
  uint32_t dig[2][MD5_DIGEST_SIZE / sizeof (uint32_t)];
  struct md5_ctx s[2];
  s[0] = s[1] = random_md5_state;
  int xfrm_diff = 0;

  if (hard_LC_COLLATE)
    {
      void *allocated = NULL;
      size_t bufsize = 0;
      const char *pa = texta;
      const char *pb = textb;
      const char *const lima = texta + lena;
      const char *const limb = textb + lenb;

      while (pa < lima || pb < limb)
        {
          size_t sizea = (pa < lima) ? xstrxfrm (NULL, pa, 0) + 1 : 0;
          size_t sizeb = (pb < limb) ? xstrxfrm (NULL, pb, 0) + 1 : 0;
          size_t total_size = sizea + sizeb;

          if (bufsize < total_size)
            {
              free (allocated);
              allocated = xmalloc (total_size);
              bufsize = total_size;
            }
          char *buf = allocated;

          if (pa < lima)
            {
              xstrxfrm (buf, pa, sizea);
              pa += strlen (pa) + 1;
            }
          if (pb < limb)
            {
              xstrxfrm (buf + sizea, pb, sizeb);
              pb += strlen (pb) + 1;
            }

          md5_process_bytes (buf, sizea, &s[0]);
          md5_process_bytes (buf + sizea, sizeb, &s[1]);

          if (xfrm_diff == 0)
            {
              xfrm_diff = compute_tiebreaker (buf, sizea, buf + sizea, sizeb);
            }
        }
      free (allocated);
    }
  else
    {
      md5_process_bytes (texta, lena, &s[0]);
      md5_process_bytes (textb, lenb, &s[1]);
    }

  md5_finish_ctx (&s[0], dig[0]);
  md5_finish_ctx (&s[1], dig[1]);

  int diff = memcmp (dig[0], dig[1], sizeof dig[0]);

  if (diff == 0)
    {
      if (hard_LC_COLLATE)
        {
          diff = xfrm_diff;
        }
      else
        {
          diff = compute_tiebreaker (texta, lena, textb, lenb);
        }
    }

  return diff;
}

/* Return the printable width of the block of memory starting at
   TEXT and ending just before LIM, counting each tab as one byte.
   FIXME: Should we generally be counting non printable chars?  */

static size_t
debug_width (char const *text, char const *lim)
{
  size_t width = mbsnwidth (text, lim - text, 0);

  for (char const *p = text; p < lim; p++)
  {
    if (*p == '\t')
    {
      width++;
    }
  }

  return width;
}

/* For debug mode, "underline" a key at the
   specified offset and screen width.  */

static void
mark_key (size_t offset, size_t width)
{
    for (size_t i = 0; i < offset; i++) {
        putchar (' ');
    }

    if (width == 0) {
        printf (_("^ no match for key\n"));
    } else {
        for (size_t i = 0; i < width; i++) {
            putchar ('_');
        }
        putchar ('\n');
    }
}

/* Return true if KEY is a numeric key.  */

static inline bool
key_numeric (struct keyfield const *key)
{
  return key && (key->numeric || key->general_numeric || key->human_numeric);
}

/* For LINE, output a debugging line that underlines KEY in LINE.
   If KEY is null, underline the whole line.  */

static char *
find_field_end (char *beg, char *lim, struct keyfield const *key)
{
  if (lim < beg)
    return lim;

  if (key->month)
    {
      char *month_lim = beg;
      getmonth (beg, &month_lim);
      return month_lim;
    }

  if (key->general_numeric)
    {
      char *num_lim;
      ignore_value (strtold (beg, &num_lim));
      return num_lim;
    }

  if (key->numeric || key->human_numeric)
    {
      char const *p = beg + (beg < lim && *beg == '-');
      if ('0' <= traverse_raw_number (&p))
        {
          unsigned char ch = *p;
          return (char *) p + (key->human_numeric && unit_order[ch]);
        }
      return beg;
    }

  return lim;
}

static void
debug_key (struct line const *line, struct keyfield const *key)
{
  char *text = line->text;
  char *beg = text;
  char *lim = text + line->length - 1;

  if (key)
    {
      if (key->sword != SIZE_MAX)
        beg = begfield (line, key);

      if (key->eword != SIZE_MAX)
        {
          lim = limfield (line, key);
          lim = MAX (beg, lim);
        }

      bool const needs_trim = (key->skipsblanks && key->sword == SIZE_MAX)
                            || key->month || key_numeric (key);

      if (needs_trim)
        {
          char saved = *lim;
          *lim = '\0';

          while (blanks[to_uchar (*beg)])
            beg++;

          lim = find_field_end (beg, lim, key);

          *lim = saved;
        }
    }

  size_t offset = debug_width (text, beg);
  size_t width = debug_width (beg, lim);
  mark_key (offset, width);
}

/* Debug LINE by underlining its keys.  */

static void
debug_line (struct line const *line)
{
  for (struct keyfield const *key = keylist; key; key = key->next)
    {
      debug_key (line, key);
    }

  if (! (unique || stable))
    {
      debug_key (line, NULL);
    }
}

/* Return whether sorting options specified for key.  */

static bool
default_key_compare (struct keyfield const *key)
{
  if (key->ignore)
    return false;
  if (key->translate)
    return false;
  if (key->skipsblanks)
    return false;
  if (key->skipeblanks)
    return false;
  if (key_numeric (key))
    return false;
  if (key->month)
    return false;
  if (key->version)
    return false;
  if (key->random)
    return false;

  return true;
}

/* Convert a key to the short options used to specify it.  */

static void
key_to_opts (struct keyfield const *key, char *opts)
{
  const struct
  {
    bool is_set;
    char option_char;
  } options[] = {
    {key->skipsblanks || key->skipeblanks, 'b'},
    {key->ignore == nondictionary,         'd'},
    {key->translate,                       'f'},
    {key->general_numeric,                 'g'},
    {key->human_numeric,                   'h'},
    {key->ignore == nonprinting,           'i'},
    {key->month,                           'M'},
    {key->numeric,                         'n'},
    {key->random,                          'R'},
    {key->reverse,                         'r'},
    {key->version,                         'V'}
  };

  for (size_t i = 0; i < sizeof (options) / sizeof (options[0]); ++i)
    {
      if (options[i].is_set)
        {
          *opts++ = options[i].option_char;
        }
    }
  *opts = '\0';
}

/* Output data independent key warnings to stderr.  */

struct numeric_key_info
{
  bool basic_numeric_field;
  bool general_numeric_field;
  bool basic_numeric_field_span;
  bool general_numeric_field_span;
};

static void
update_numeric_key_info (struct keyfield const *key,
                         struct numeric_key_info *info)
{
  if (key_numeric (key))
    {
      if (key->general_numeric)
        info->general_numeric_field = true;
      else
        info->basic_numeric_field = true;
    }
}

static void
warn_obsolescent_key (struct keyfield const *key)
{
  if (!key->traditional_used)
    return;

  char tmp[INT_BUFSIZE_BOUND (uintmax_t)];
  char obuf[INT_BUFSIZE_BOUND (uintmax_t) * 2 + 4];
  char nbuf[INT_BUFSIZE_BOUND (uintmax_t) * 2 + 5];
  char *po = obuf;
  char *pn = nbuf;

  size_t sword = key->sword;
  if (sword == SIZE_MAX)
    sword = 0;

  po = stpcpy (stpcpy (po, "+"), umaxtostr (sword, tmp));
  pn = stpcpy (stpcpy (pn, "-k "), umaxtostr (sword + 1, tmp));

  if (key->eword != SIZE_MAX)
    {
      stpcpy (stpcpy (po, " -"), umaxtostr (key->eword + 1, tmp));
      stpcpy (stpcpy (pn, ","),
              umaxtostr (key->eword + 1 + (key->echar == SIZE_MAX), tmp));
    }
  error (0, 0, _("obsolescent key %s used; consider %s instead"),
         quote_n (0, obuf), quote_n (1, nbuf));
}

static void
warn_zero_width_key (struct keyfield const *key, unsigned long keynum)
{
  if (key->sword != SIZE_MAX && key->eword < key->sword)
    error (0, 0, _("key %lu has zero width and will be ignored"), keynum);
}

static void
warn_significant_leading_blanks (struct keyfield const *key, unsigned long keynum)
{
  if (tab != TAB_DEFAULT)
    return;

  bool zero_width = key->sword != SIZE_MAX && key->eword < key->sword;
  if (zero_width)
    return;

  bool line_offset = key->eword == 0 && key->echar != 0;
  if (line_offset)
    return;

  bool implicit_skip = key_numeric (key) || key->month;
  bool needs_b_flag = ((!key->skipsblanks && !implicit_skip)
                       || (!key->skipsblanks && key->schar)
                       || (!key->skipeblanks && key->echar));

  if (needs_b_flag)
    error (0, 0, _("leading blanks are significant in key %lu; "
                   "consider also specifying 'b'"), keynum);
}

static void
warn_numeric_span (struct keyfield const *key, unsigned long keynum,
                   struct numeric_key_info *info)
{
  if (!key_numeric (key))
    return;

  size_t sword = key->sword + 1;
  if (sword == 0)
    sword = 1;

  size_t eword = key->eword + 1;

  if (eword == 0 || sword < eword)
    {
      error (0, 0, _("key %lu is numeric and spans multiple fields"), keynum);
      if (key->general_numeric)
        info->general_numeric_field_span = true;
      else
        info->basic_numeric_field_span = true;
    }
}

static void
update_unused_global_options (struct keyfield *unused_gkey,
                              struct keyfield const *key)
{
  if (unused_gkey->ignore && unused_gkey->ignore == key->ignore)
    unused_gkey->ignore = NULL;
  if (unused_gkey->translate && unused_gkey->translate == key->translate)
    unused_gkey->translate = NULL;

  unused_gkey->skipsblanks &= !key->skipsblanks;
  unused_gkey->skipeblanks &= !key->skipeblanks;
  unused_gkey->month &= !key->month;
  unused_gkey->numeric &= !key->numeric;
  unused_gkey->general_numeric &= !key->general_numeric;
  unused_gkey->human_numeric &= !key->human_numeric;
  unused_gkey->random &= !key->random;
  unused_gkey->version &= !key->version;
  unused_gkey->reverse &= !key->reverse;
}

static void
warn_locale_specific_numeric (struct numeric_key_info const *info)
{
  bool number_locale_warned = false;

  if (info->basic_numeric_field_span)
    {
      if (tab == TAB_DEFAULT
          ? thousands_sep != NON_CHAR && isblank (to_uchar (thousands_sep))
          : tab == thousands_sep)
        {
          error (0, 0,
                 _("field separator %s is treated as a "
                   "group separator in numbers"),
                 quote (((char []) {thousands_sep, 0})));
          number_locale_warned = true;
        }
    }

  if (info->basic_numeric_field_span || info->general_numeric_field_span)
    {
      if (tab == TAB_DEFAULT
          ? thousands_sep != NON_CHAR && isblank (to_uchar (decimal_point))
          : tab == decimal_point)
        {
          error (0, 0,
                 _("field separator %s is treated as a "
                   "decimal point in numbers"),
                 quote (((char []) {decimal_point, 0})));
          number_locale_warned = true;
        }
      else if (tab == '-')
        error (0, 0,
               _("field separator %s is treated as a "
                 "minus sign in numbers"),
               quote ("-"));
      else if (info->general_numeric_field_span && tab == '+')
        error (0, 0,
               _("field separator %s is treated as a "
                 "plus sign in numbers"),
               quote ("+"));
    }

  if ((info->basic_numeric_field || info->general_numeric_field)
      && !number_locale_warned)
    error (0, 0, _("numbers use %s as a decimal point in this locale"),
           quote (((char []) {decimal_point, 0})));

  if (info->basic_numeric_field && thousands_sep_ignored)
    error (0, 0,
           _("the multi-byte number group separator "
             "in this locale is not supported"));
}

static void
warn_ignored_global_options (struct keyfield const *unused_gkey)
{
  struct keyfield temp_ugkey = *unused_gkey;

  if (!default_key_compare (&temp_ugkey)
      || (temp_ugkey.reverse && (stable || unique) && keylist))
    {
      bool ugkey_reverse = temp_ugkey.reverse;
      if (!(stable || unique))
        temp_ugkey.reverse = false;

      char opts[sizeof short_options];
      key_to_opts (&temp_ugkey, opts);

      if (opts[0])
        error (0, 0,
               ngettext ("option '-%s' is ignored",
                         "options '-%s' are ignored",
                         select_plural (strlen (opts))),
               opts);

      temp_ugkey.reverse = ugkey_reverse;
    }

  if (temp_ugkey.reverse && !(stable || unique) && keylist)
    error (0, 0, _("option '-r' only applies to last-resort comparison"));
}

static void
key_warnings (struct keyfield const *gkey, bool gkey_only)
{
  struct keyfield unused_gkey = *gkey;
  struct numeric_key_info num_info = { false, false, false, false };

  unsigned long keynum = 1;
  for (struct keyfield const *key = keylist; key; key = key->next, keynum++)
    {
      update_numeric_key_info (key, &num_info);

      warn_obsolescent_key (key);
      warn_zero_width_key (key, keynum);

      if (!gkey_only)
        {
          warn_significant_leading_blanks (key, keynum);
          warn_numeric_span (key, keynum, &num_info);
        }

      update_unused_global_options (&unused_gkey, key);
    }

  warn_locale_specific_numeric (&num_info);
  warn_ignored_global_options (&unused_gkey);
}

/* Return either the sense of DIFF or its reverse, depending on REVERSED.
   If REVERSED, do not simply negate DIFF as that can mishandle INT_MIN.  */

static int
diff_reversed (int diff, bool reversed)
{
  if (reversed)
    {
      return _GL_CMP (0, diff);
    }
  return diff;
}

/* Compare two lines A and B trying every key in sequence until there
   are no more keys or a difference is found. */

static int
dispatch_comparison (struct keyfield const *key,
                     char const *ta, size_t tlena,
                     char const *tb, size_t tlenb)
{
  if (key->numeric)
    return numcompare (ta, tb);
  if (key->general_numeric)
    return general_numcompare (ta, tb);
  if (key->human_numeric)
    return human_numcompare (ta, tb);
  if (key->month)
    return getmonth (ta, NULL) - getmonth (tb, NULL);
  if (key->random)
    return compare_random (ta, tlena, tb, tlenb);
  if (key->version)
    return filenvercmp (ta, tlena, tb, tlenb);

  if (tlena == 0)
    return -NONZERO (tlenb);
  if (tlenb == 0)
    return 1;

  return xmemcoll0 (ta, tlena + 1, tb, tlenb + 1);
}

static size_t
transform_string (char *dest, char const *src, size_t len,
                  bool const *ignore, char const *translate)
{
  size_t new_len = 0;
  for (size_t i = 0; i < len; ++i)
    {
      unsigned char c = to_uchar (src[i]);
      if (! (ignore && ignore[c]))
        {
          dest[new_len++] = translate ? translate[c] : src[i];
        }
    }
  dest[new_len] = '\0';
  return new_len;
}

static int
compare_special (struct keyfield const *key,
                 char *texta, size_t lena,
                 char *textb, size_t lenb)
{
  if (!key->ignore && !key->translate)
    {
      char enda = texta[lena];
      char endb = textb[lenb];
      texta[lena] = '\0';
      textb[lenb] = '\0';

      int diff = dispatch_comparison (key, texta, lena, textb, lenb);

      texta[lena] = enda;
      textb[lenb] = endb;
      return diff;
    }

  void *allocated = NULL;
  char stackbuf[4000];
  char *buf;
  size_t size = lena + 1 + lenb + 1;

  if (size <= sizeof stackbuf)
    buf = stackbuf;
  else
    buf = allocated = xmalloc (size);

  char *ta = buf;
  char *tb = ta + lena + 1;

  size_t tlena = transform_string (ta, texta, lena, key->ignore, key->translate);
  size_t tlenb = transform_string (tb, textb, lenb, key->ignore, key->translate);

  int diff = dispatch_comparison (key, ta, tlena, tb, tlenb);

  free (allocated);
  return diff;
}

static int
compare_with_ignore (char const *texta, char const *lima,
                     char const *textb, char const *limb,
                     bool const *ignore, char const *translate)
{
  while (true)
    {
      while (texta < lima && ignore[to_uchar (*texta)])
        ++texta;
      while (textb < limb && ignore[to_uchar (*textb)])
        ++textb;

      bool a_has_chars = texta < lima;
      bool b_has_chars = textb < limb;

      if (!a_has_chars || !b_has_chars)
        return a_has_chars - b_has_chars;

      unsigned char ca = to_uchar (*texta);
      unsigned char cb = to_uchar (*textb);

      int diff = (translate ? to_uchar (translate[ca]) : ca)
               - (translate ? to_uchar (translate[cb]) : cb);

      if (diff)
        return diff;

      ++texta;
      ++textb;
    }
}

static int
compare_simple (char const *texta, char const *textb,
                size_t lena, size_t lenb,
                char const *translate)
{
  size_t lenmin = MIN (lena, lenb);
  int diff = 0;

  if (lenmin > 0)
    {
      if (translate)
        {
          for (size_t i = 0; i < lenmin; ++i)
            {
              diff = (to_uchar (translate[to_uchar (texta[i])])
                      - to_uchar (translate[to_uchar (textb[i])]));
              if (diff)
                return diff;
            }
        }
      else
        {
          diff = memcmp (texta, textb, lenmin);
        }
    }

  if (diff == 0)
    diff = _GL_CMP (lena, lenb);

  return diff;
}

static void
get_next_field (struct line const *line, struct keyfield const *key,
                char **text, char **lim)
{
  if (key->eword != SIZE_MAX)
    *lim = limfield (line, key);
  else
    *lim = line->text + line->length - 1;

  if (key->sword != SIZE_MAX)
    *text = begfield (line, key);
  else
    {
      *text = line->text;
      if (key->skipsblanks)
        {
          while (*text < *lim && blanks[to_uchar (**text)])
            ++(*text);
        }
    }
}

static int
keycompare (struct line const *a, struct line const *b)
{
  struct keyfield *key = keylist;
  char *texta = a->keybeg;
  char *textb = b->keybeg;
  char *lima = a->keylim;
  char *limb = b->keylim;
  int diff;

  while (true)
    {
      char *current_lima = MAX (texta, lima);
      char *current_limb = MAX (textb, limb);

      size_t lena = current_lima - texta;
      size_t lenb = current_limb - textb;

      if (hard_LC_COLLATE || key_numeric (key) || key->month
          || key->random || key->version)
        {
          diff = compare_special (key, texta, lena, textb, lenb);
        }
      else if (key->ignore)
        {
          diff = compare_with_ignore (texta, current_lima, textb, current_limb,
                                      key->ignore, key->translate);
        }
      else
        {
          diff = compare_simple (texta, textb, lena, lenb, key->translate);
        }

      if (diff)
        break;

      key = key->next;
      if (!key)
        return 0;

      get_next_field (a, key, &texta, &lima);
      get_next_field (b, key, &textb, &limb);
    }

  return diff_reversed (diff, key->reverse);
}

/* Compare two lines A and B, returning negative, zero, or positive
   depending on whether A compares less than, equal to, or greater than B. */

static int
compare (struct line const *a, struct line const *b)
{
  int diff;

  if (keylist)
    {
      diff = keycompare (a, b);
      if (diff || unique || stable)
        {
          return diff;
        }
    }

  const size_t alen = a->length - 1;
  const size_t blen = b->length - 1;

  if (alen == 0 || blen == 0)
    {
      diff = (alen > blen) - (alen < blen);
    }
  else if (hard_LC_COLLATE)
    {
      diff = xmemcoll0 (a->text, a->length, b->text, b->length);
    }
  else
    {
      const size_t min_len = (alen < blen) ? alen : blen;
      diff = memcmp (a->text, b->text, min_len);
      if (diff == 0)
        {
          diff = (alen > blen) - (alen < blen);
        }
    }

  return diff_reversed (diff, reverse);
}

/* Write LINE to output stream FP; the output file's name is
   OUTPUT_FILE if OUTPUT_FILE is non-null, and is the standard output
   otherwise.  If debugging is enabled and FP is standard output,
   append some debugging information.  */

static void
write_debug_line (struct line const *line, FILE *fp, char const *output_file)
{
  for (size_t i = 0; i < line->length; ++i)
    {
      char wc = line->text[i];
      int is_last_char = (i == line->length - 1);

      if (wc == '\t')
        {
          wc = '>';
        }
      else if (is_last_char)
        {
          wc = '\n';
        }

      if (fputc (wc, fp) == EOF)
        sort_die (_("write failed"), output_file);
    }

  debug_line (line);
}

static void
write_line (struct line const *line, FILE *fp, char const *output_file)
{
  if (!output_file && debug)
    {
      write_debug_line (line, fp, output_file);
    }
  else
    {
      size_t n_bytes = line->length;

      if (n_bytes > 0)
        {
          if (fwrite (line->text, 1, n_bytes - 1, fp) != n_bytes - 1)
            sort_die (_("write failed"), output_file);
        }

      if (fputc (eolchar, fp) == EOF)
        sort_die (_("write failed"), output_file);
    }
}

/* Check that the lines read from FILE_NAME come in order.  Return
   true if they are in order.  If CHECKONLY == 'c', also print a
   diagnostic (FILE_NAME, line number, contents of line) to stderr if
   they are not in order.  */

static void
report_disorder (char const *file_name, struct line const *line,
                 uintmax_t line_num)
{
  char hr_buf[INT_BUFSIZE_BOUND (uintmax_t)];
  fprintf (stderr, _("%s: %s:%s: disorder: "),
           program_name, file_name, umaxtostr (line_num, hr_buf));
  write_line (line, stderr, _("standard error"));
}

static void
save_line (struct line *dest, size_t *alloc, struct line const *src)
{
  if (*alloc < src->length)
    {
      size_t new_alloc = *alloc ? *alloc * 2 : src->length;
      while (new_alloc < src->length)
        new_alloc *= 2;

      dest->text = xrealloc (dest->text, new_alloc);
      *alloc = new_alloc;
    }
  memcpy (dest->text, src->text, src->length);
  dest->length = src->length;

  if (keylist)
    {
      dest->keybeg = dest->text + (src->keybeg - src->text);
      dest->keylim = dest->text + (src->keylim - src->text);
    }
}

static bool
check (char const *file_name, char checkonly)
{
  FILE *fp = xfopen (file_name, "r");
  struct buffer buf;
  struct line prev_line;
  size_t prev_line_alloc = 0;
  uintmax_t lines_before_buf = 0;
  bool ordered = true;
  bool has_prev_line = false;
  const bool nonunique = !unique;

  initbuf (&buf, sizeof (struct line),
           MAX (merge_buffer_size, sort_size));
  prev_line.text = NULL;

  while (ordered && fillbuf (&buf, fp, file_name))
    {
      struct line const *line_base = buffer_linestart (&buf);
      struct line const *line_lim = buffer_linelim (&buf);

      if (has_prev_line)
        {
          if (nonunique <= compare (&prev_line, line_base))
            {
              ordered = false;
              if (checkonly == 'c')
                report_disorder (file_name, line_base, lines_before_buf + 1);
            }
        }

      if (!ordered)
        break;

      for (struct line const *l = line_base; l < line_lim - 1; ++l)
        {
          if (nonunique <= compare (l + 1, l))
            {
              ordered = false;
              if (checkonly == 'c')
                {
                  uintmax_t line_offset = (l + 1) - line_base;
                  report_disorder (file_name, l + 1,
                                   lines_before_buf + line_offset + 1);
                }
              break;
            }
        }

      if (buf.nlines > 0)
        {
          save_line (&prev_line, &prev_line_alloc, line_lim - 1);
          has_prev_line = true;
        }

      lines_before_buf += buf.nlines;
    }

  xfclose (fp, file_name);
  free (buf.buf);
  free (prev_line.text);
  return ordered;
}

/* Open FILES (there are NFILES of them) and store the resulting array
   of stream pointers into (*PFPS).  Allocate the array.  Return the
   number of successfully opened files, setting errno if this value is
   less than NFILES.  */

static size_t
open_input_files (struct sortfile *files, size_t nfiles, FILE ***pfps)
{
  FILE **fps = *pfps = xnmalloc (nfiles, sizeof *fps);

  for (size_t i = 0; i < nfiles; i++)
    {
      bool is_compressed_temp = files[i].temp
                                && files[i].temp->state != UNCOMPRESSED;

      if (is_compressed_temp)
        {
          fps[i] = open_temp (files[i].temp);
        }
      else
        {
          fps[i] = stream_open (files[i].name, "r");
        }

      if (!fps[i])
        {
          return i;
        }
    }

  return nfiles;
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   FPS is the vector of open stream corresponding to the files.
   Close input and output streams before returning.
   OUTPUT_FILE gives the name of the output file.  If it is null,
   the output file is standard output.  */

struct unique_state
{
  struct line line;
  struct line const *saved;
  size_t alloc;
};

static void
save_for_unique (struct unique_state *st, struct line const *line)
{
  if (st->alloc < line->length)
    {
      size_t new_alloc = st->alloc ? st->alloc * 2 : line->length;
      while (new_alloc < line->length)
        new_alloc *= 2;
      st->alloc = new_alloc;
      free (st->line.text);
      st->line.text = xmalloc (st->alloc);
    }

  st->line.length = line->length;
  memcpy (st->line.text, line->text, line->length);

  if (keylist)
    {
      st->line.keybeg = st->line.text + (line->keybeg - line->text);
      st->line.keylim = st->line.text + (line->keylim - line->text);
    }
  st->saved = &st->line;
}

static void
process_unique (struct unique_state *st, struct line const *smallest,
                FILE *ofp, char const *output_file)
{
  if (st->saved && compare (st->saved, smallest))
    {
      write_line (st->saved, ofp, output_file);
      st->saved = NULL;
    }
  if (!st->saved)
    {
      save_for_unique (st, smallest);
    }
}

static void
reinsert_file (size_t *ord, size_t nfiles, struct line const * const *cur)
{
  size_t file_to_reinsert = ord[0];
  size_t lo = 1;
  size_t hi = nfiles;

  while (lo < hi)
    {
      size_t mid = lo + (hi - lo) / 2;
      int cmp = compare (cur[file_to_reinsert], cur[ord[mid]]);
      if (cmp < 0 || (cmp == 0 && file_to_reinsert < ord[mid]))
        hi = mid;
      else
        lo = mid + 1;
    }

  size_t new_pos = lo - 1;
  memmove (&ord[0], &ord[1], new_pos * sizeof (*ord));
  ord[new_pos] = file_to_reinsert;
}

static void
build_initial_order(size_t *ord, size_t nfiles, struct line const * const *cur)
{
  for (size_t i = 0; i < nfiles; ++i)
    ord[i] = i;

  for (size_t i = 1; i < nfiles; ++i)
    if (0 < compare (cur[ord[i - 1]], cur[ord[i]]))
      {
        size_t temp = ord[i - 1];
        ord[i - 1] = ord[i];
        ord[i] = temp;
        i = 0;
      }
}

static void
mergefps (struct sortfile *files, size_t ntemps, size_t nfiles,
          FILE *ofp, char const *output_file, FILE **fps)
{
  struct buffer *buffers = xnmalloc (nfiles, sizeof *buffers);
  struct line const **cur = xnmalloc (nfiles, sizeof *cur);
  struct line const **base = xnmalloc (nfiles, sizeof *base);
  size_t *ord = xnmalloc (nfiles, sizeof *ord);
  struct unique_state u_state = { {NULL, 0, NULL, NULL}, NULL, 0 };

  for (size_t i = 0; i < nfiles; )
    {
      initbuf (&buffers[i], sizeof (struct line),
               MAX (merge_buffer_size, sort_size / nfiles));
      if (fillbuf (&buffers[i], fps[i], files[i].name))
        {
          struct line const *linelim = buffer_linelim (&buffers[i]);
          cur[i] = linelim - 1;
          base[i] = linelim - buffers[i].nlines;
          i++;
        }
      else
        {
          xfclose (fps[i], files[i].name);
          if (i < ntemps)
            {
              ntemps--;
              zaptemp (files[i].name);
            }
          free (buffers[i].buf);
          size_t n_to_move = nfiles - 1 - i;
          if (n_to_move > 0)
            {
              memmove (&files[i], &files[i + 1], n_to_move * sizeof (*files));
              memmove (&fps[i], &fps[i + 1], n_to_move * sizeof (*fps));
            }
          nfiles--;
        }
    }

  build_initial_order(ord, nfiles, cur);

  while (nfiles)
    {
      size_t smallest_idx = ord[0];
      struct line const *smallest = cur[smallest_idx];

      if (unique)
        process_unique (&u_state, smallest, ofp, output_file);
      else
        write_line (smallest, ofp, output_file);

      if (base[smallest_idx] < smallest)
        {
          cur[smallest_idx] = smallest - 1;
        }
      else
        {
          if (fillbuf (&buffers[smallest_idx], fps[smallest_idx], files[smallest_idx].name))
            {
              struct line const *linelim = buffer_linelim (&buffers[smallest_idx]);
              cur[smallest_idx] = linelim - 1;
              base[smallest_idx] = linelim - buffers[smallest_idx].nlines;
            }
          else
            {
              xfclose (fps[smallest_idx], files[smallest_idx].name);
              if (smallest_idx < ntemps)
                {
                  ntemps--;
                  zaptemp (files[smallest_idx].name);
                }
              free (buffers[smallest_idx].buf);

              for (size_t i = 1; i < nfiles; ++i)
                if (ord[i] > smallest_idx)
                  --ord[i];

              size_t n_to_move = nfiles - 1 - smallest_idx;
              if (n_to_move > 0)
                {
                  memmove(&files[smallest_idx], &files[smallest_idx + 1], n_to_move * sizeof(*files));
                  memmove(&fps[smallest_idx], &fps[smallest_idx + 1], n_to_move * sizeof(*fps));
                  memmove(&buffers[smallest_idx], &buffers[smallest_idx + 1], n_to_move * sizeof(*buffers));
                  memmove(&cur[smallest_idx], &cur[smallest_idx + 1], n_to_move * sizeof(*cur));
                  memmove(&base[smallest_idx], &base[smallest_idx + 1], n_to_move * sizeof(*base));
                }

              nfiles--;
              memmove (&ord[0], &ord[1], nfiles * sizeof (*ord));
              continue;
            }
        }
      reinsert_file(ord, nfiles, cur);
    }

  if (unique && u_state.saved)
    {
      write_line (u_state.saved, ofp, output_file);
      free (u_state.line.text);
    }

  xfclose (ofp, output_file);
  free (fps);
  free (buffers);
  free (ord);
  free (base);
  free (cur);
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   Close input and output files before returning.
   OUTPUT_FILE gives the name of the output file.

   Return the number of files successfully merged.  This number can be
   less than NFILES if we ran low on file descriptors, but in this
   case it is never less than 2.  */

static size_t
mergefiles (struct sortfile *files, size_t ntemps, size_t nfiles,
            FILE *ofp, char const *output_file)
{
  FILE **fps = NULL;
  size_t nopened = open_input_files (files, nfiles, &fps);

  const size_t min_files_for_partial_merge = 2;
  if (nopened < nfiles && nopened < min_files_for_partial_merge)
    {
      sort_die (_("open failed"), files[nopened].name);
    }

  mergefps (files, ntemps, nopened, ofp, output_file, fps);
  return nopened;
}

/* Merge into T (of size NLINES) the two sorted arrays of lines
   LO (with NLINES / 2 members), and
   T - (NLINES / 2) (with NLINES - NLINES / 2 members).
   T and LO point just past their respective arrays, and the arrays
   are in reverse order.  NLINES must be at least 2.  */

static void
mergelines (struct line *restrict t, size_t nlines,
            struct line const *restrict lo)
{
  size_t nlo = nlines / 2;
  size_t nhi = nlines - nlo;
  struct line *hi = t - nlo;

  while (nlo > 0 && nhi > 0)
    {
      if (compare (lo - 1, hi - 1) <= 0)
        {
          *--t = *--lo;
          nlo--;
        }
      else
        {
          *--t = *--hi;
          nhi--;
        }
    }

  while (nlo > 0)
    {
      *--t = *--lo;
      nlo--;
    }
}

/* Sort the array LINES with NLINES members, using TEMP for temporary space.
   Do this all within one thread.  NLINES must be at least 2.
   If TO_TEMP, put the sorted output into TEMP, and TEMP is as large as LINES.
   Otherwise the sort is in-place and TEMP is half-sized.
   The input and output arrays are in reverse order, and LINES and
   TEMP point just past the end of their respective arrays.

   Use a recursive divide-and-conquer algorithm, in the style
   suggested by Knuth volume 3 (2nd edition), exercise 5.2.4-23.  Use
   the optimization suggested by exercise 5.2.4-10; this requires room
   for only 1.5*N lines, rather than the usual 2*N lines.  Knuth
   writes that this memory optimization was originally published by
   D. A. Bell, Comp J. 1 (1958), 75.  */

static void
sequential_sort (struct line *restrict lines, size_t nlines,
                 struct line *restrict temp, bool to_temp)
{
  if (nlines < 2)
    {
      if (nlines == 1 && to_temp)
        {
          temp[0] = lines[0];
        }
    }
  else if (nlines == 2)
    {
      int swap = (0 < compare (&lines[0], &lines[1]));
      if (to_temp)
        {
          temp[0] = lines[swap ? 1 : 0];
          temp[1] = lines[swap ? 0 : 1];
        }
      else if (swap)
        {
          struct line t = lines[0];
          lines[0] = lines[1];
          lines[1] = t;
        }
    }
  else
    {
      size_t nlo = nlines / 2;
      size_t nhi = nlines - nlo;
      struct line *lo = lines;
      struct line *hi = lines + nlo;
      struct line *temp_lo = temp;
      struct line *temp_hi = temp + nlo;

      sequential_sort (hi, nhi, to_temp ? temp_hi : temp, to_temp);
      sequential_sort (lo, nlo, temp_lo, !to_temp);

      struct line *dest = to_temp ? temp : lines;
      const struct line *sorted_lo = to_temp ? lines : temp;
      mergelines (dest, nlines, sorted_lo);
    }
}

static struct merge_node *init_node (struct merge_node *restrict,
                                     struct merge_node *restrict,
                                     struct line *, size_t, size_t, bool);


/* Create and return a merge tree for NTHREADS threads, sorting NLINES
   lines, with destination DEST.  */
static struct merge_node *
merge_tree_init (size_t nthreads, size_t nlines, struct line *dest)
{
  struct merge_node *merge_tree = xcalloc (2 * nthreads, sizeof (*merge_tree));

  struct merge_node *root = merge_tree;

  root->nlo = nlines;
  root->nhi = nlines;
  root->level = MERGE_END;

  if (pthread_mutex_init (&root->lock, nullptr) != 0)
    {
      perror ("pthread_mutex_init");
      abort ();
    }

  init_node (root, root + 1, dest, nthreads, nlines, false);
  return merge_tree;
}

/* Destroy the merge tree. */
static void
merge_tree_destroy (size_t nthreads, struct merge_node *merge_tree)
{
  if (!merge_tree)
    {
      return;
    }

  const size_t n_nodes = nthreads * 2;
  for (size_t i = 0; i < n_nodes; ++i)
    {
      int ret = pthread_mutex_destroy (&merge_tree[i].lock);
      (void) ret;
      assert(ret == 0);
    }

  free (merge_tree);
}

/* Initialize a merge tree node and its descendants.  The node's
   parent is PARENT.  The node and its descendants are taken from the
   array of nodes NODE_POOL.  Their destination starts at DEST; they
   will consume NTHREADS threads.  The total number of sort lines is
   TOTAL_LINES.  IS_LO_CHILD is true if the node is the low child of
   its parent.  */

static struct merge_node *
init_node (struct merge_node *restrict parent,
           struct merge_node *restrict node_pool,
           struct line *dest, size_t nthreads,
           size_t total_lines, bool is_lo_child)
{
  size_t nlines;
  struct line **parent_end;

  if (is_lo_child)
    {
      nlines = parent->nlo;
      parent_end = &parent->end_lo;
    }
  else
    {
      nlines = parent->nhi;
      parent_end = &parent->end_hi;
    }

  size_t nlo = nlines / 2;
  size_t nhi = nlines - nlo;
  struct line *lo_lines = dest - total_lines;
  struct line *hi_lines = lo_lines - nlo;

  struct merge_node *node = node_pool++;
  node->lo = lo_lines;
  node->end_lo = lo_lines;
  node->hi = hi_lines;
  node->end_hi = hi_lines;
  node->dest = parent_end;
  node->nlo = nlo;
  node->nhi = nhi;
  node->parent = parent;
  node->level = parent->level + 1;
  node->queued = false;
  node->lo_child = NULL;
  node->hi_child = NULL;

  if (pthread_mutex_init (&node->lock, NULL) != 0)
    {
      abort ();
    }

  if (nthreads > 1)
    {
      size_t lo_threads = nthreads / 2;
      size_t hi_threads = nthreads - lo_threads;
      node->lo_child = node_pool;
      node_pool = init_node (node, node_pool, lo_lines, lo_threads,
                             total_lines, true);
      node->hi_child = node_pool;
      node_pool = init_node (node, node_pool, hi_lines, hi_threads,
                             total_lines, false);
    }
    
  return node_pool;
}


/* Compare two merge nodes A and B for priority.  */

static int
compare_nodes (void const *a, void const *b)
{
  struct merge_node const *nodea = (struct merge_node const *)a;
  struct merge_node const *nodeb = (struct merge_node const *)b;

  if (nodea->level != nodeb->level)
    {
      return (nodea->level > nodeb->level) - (nodea->level < nodeb->level);
    }

  unsigned long long suma = (unsigned long long)nodea->nlo + nodea->nhi;
  unsigned long long sumb = (unsigned long long)nodeb->nlo + nodeb->nhi;

  return (suma > sumb) - (suma < sumb);
}

/* Lock a merge tree NODE.  */

static inline void
lock_node (struct merge_node *node)
{
  if (!node)
    {
      /* This is a programming error. Crashing is the safest action. */
      abort ();
    }

  int const ret = pthread_mutex_lock (&node->lock);
  if (ret != 0)
    {
      /* A failure to lock is a fatal, unrecoverable error. */
      /* Log the error and terminate to prevent data corruption. */
      fprintf (stderr, "Fatal: pthread_mutex_lock failed: %s\n",
               strerror (ret));
      abort ();
    }
}

/* Unlock a merge tree NODE. */

static inline void
unlock_node (struct merge_node *node)
{
  if (!node)
    {
      return;
    }

  if (pthread_mutex_unlock (&node->lock) != 0)
    {
      abort ();
    }
}

/* Destroy merge QUEUE. */

static void
queue_destroy (struct merge_node_queue *queue)
{
  if (!queue)
    {
      return;
    }

  heap_free (queue->priority_queue);
  (void) pthread_cond_destroy (&queue->cond);
  (void) pthread_mutex_destroy (&queue->mutex);
}

/* Initialize merge QUEUE, allocating space suitable for a maximum of
   NTHREADS threads.  */

static void
queue_init (struct merge_node_queue *queue, size_t nthreads)
{
  /* Though it's highly unlikely all nodes are in the heap at the same
     time, the heap should accommodate all of them.  Counting a null
     dummy head for the heap, reserve 2 * NTHREADS nodes.  */
  queue->priority_queue = heap_alloc (compare_nodes, 2 * nthreads);
  if (!queue->priority_queue)
    {
      perror ("Error allocating priority queue");
      exit (EXIT_FAILURE);
    }

  if (pthread_mutex_init (&queue->mutex, NULL) != 0)
    {
      heap_free (queue->priority_queue);
      perror ("Error initializing mutex");
      exit (EXIT_FAILURE);
    }

  if (pthread_cond_init (&queue->cond, NULL) != 0)
    {
      pthread_mutex_destroy (&queue->mutex);
      heap_free (queue->priority_queue);
      perror ("Error initializing condition variable");
      exit (EXIT_FAILURE);
    }
}

/* Insert NODE into QUEUE.  The caller either holds a lock on NODE, or
   does not need to lock NODE.  */

static int
queue_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (!queue || !node)
    {
      return EINVAL;
    }

  int ret = pthread_mutex_lock (&queue->mutex);
  if (ret != 0)
    {
      return ret;
    }

  if (heap_insert (queue->priority_queue, node) != 0)
    {
      ret = ENOMEM; /* Or an appropriate error for heap_insert failure */
      goto unlock;
    }

  node->queued = true;
  ret = pthread_cond_signal (&queue->cond);

unlock:
  {
    int unlock_ret = pthread_mutex_unlock (&queue->mutex);
    if (unlock_ret != 0)
      {
        return unlock_ret;
      }
  }

  return ret;
}

/* Pop the top node off the priority QUEUE, lock the node, return it.  */

static struct merge_node *
queue_pop(struct merge_node_queue *queue)
{
    struct merge_node *node;

    if (pthread_mutex_lock(&queue->mutex) != 0)
    {
        /* In a real-world scenario, this should be handled,
         * possibly by aborting or returning an error.
         * For this refactoring, we maintain original behavior. */
    }

    for (;;)
    {
        node = heap_remove_top(queue->priority_queue);
        if (node != NULL)
        {
            break;
        }
        if (pthread_cond_wait(&queue->cond, &queue->mutex) != 0)
        {
            /* Error handling as above. */
        }
    }

    if (pthread_mutex_unlock(&queue->mutex) != 0)
    {
        /* Error handling as above. */
    }

    lock_node(node);
    node->queued = false;
    return node;
}

/* Output LINE to TFP, unless -u is specified and the line compares
   equal to the previous line.  TEMP_OUTPUT is the name of TFP, or
   is null if TFP is standard output.

   This function does not save the line for comparison later, so it is
   appropriate only for internal sort.  */

static void
write_unique (struct line const *line, FILE *tfp, char const *temp_output)
{
  if (!unique)
    {
      write_line (line, tfp, temp_output);
      return;
    }

  if (saved_line.text && !compare (line, &saved_line))
    {
      return;
    }

  saved_line = *line;
  write_line (line, tfp, temp_output);
}

/* Merge the lines currently available to a NODE in the binary
   merge tree.  Merge a number of lines appropriate for this merge
   level, assuming TOTAL_LINES is the total number of lines.

   If merging at the top level, send output to TFP.  TEMP_OUTPUT is
   the name of TFP, or is null if TFP is standard output.  */

static void
mergelines_node (struct merge_node *restrict node, size_t total_lines,
                 FILE *tfp, char const *temp_output)
{
  struct line *const lo_orig = node->lo;
  struct line *const hi_orig = node->hi;
  size_t to_merge = MAX_MERGE (total_lines, node->level);
  const bool to_buffer = (node->level > MERGE_ROOT);
  struct line *dest = to_buffer ? *node->dest : NULL;

  while (to_merge-- > 0)
    {
      struct line *winner;
      const bool lo_available = (node->lo != node->end_lo);
      const bool hi_available = (node->hi != node->end_hi);

      if (lo_available && (!hi_available || compare (node->lo - 1, node->hi - 1) <= 0))
        {
          winner = --node->lo;
        }
      else if (hi_available)
        {
          winner = --node->hi;
        }
      else
        {
          break;
        }

      if (to_buffer)
        {
          *--dest = *winner;
        }
      else
        {
          write_unique (winner, tfp, temp_output);
        }
    }

  if (to_buffer)
    {
      *node->dest = dest;
    }

  node->nlo -= (size_t) (lo_orig - node->lo);
  node->nhi -= (size_t) (hi_orig - node->hi);
}

/* Into QUEUE, insert NODE if it is not already queued, and if one of
   NODE's children has available lines and the other either has
   available lines or has exhausted its lines.  */

static void
queue_check_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (!node->queued)
    {
      const bool lo_avail = (node->lo != node->end_lo);
      const bool hi_avail = (node->hi != node->end_hi);
      bool should_insert;

      if (lo_avail)
        {
          should_insert = hi_avail || (node->nhi == 0);
        }
      else
        {
          should_insert = hi_avail && (node->nlo == 0);
        }

      if (should_insert)
        {
          queue_insert (queue, node);
        }
    }
}

/* Into QUEUE, insert NODE's parent if the parent can now be worked on.  */

static void
queue_check_insert_parent (struct merge_node_queue *queue,
                           struct merge_node *node)
{
  if (!node || !node->parent)
    {
      return;
    }

  if (node->level > MERGE_ROOT)
    {
      lock_node (node->parent);
      queue_check_insert (queue, node->parent);
      unlock_node (node->parent);
    }
  else
    {
      /* Check if the root node has finished merging its children. */
      const bool is_root_node_finished = (node->nlo == 0 && node->nhi == 0);
      if (is_root_node_finished)
        {
          /* Insert the final MERGE_END node into the queue. */
          queue_insert (queue, node->parent);
        }
    }
}

/* Repeatedly pop QUEUE for a node with lines to merge, and merge at least
   some of those lines, until the MERGE_END node is popped.
   TOTAL_LINES is the total number of lines.  If merging at the top
   level, send output to TFP.  TEMP_OUTPUT is the name of TFP, or is
   null if TFP is standard output.  */

static void
merge_loop (struct merge_node_queue *queue,
            size_t total_lines, FILE *tfp, char const *temp_output)
{
  struct merge_node *node;

  while ((node = queue_pop (queue)) && node->level != MERGE_END)
    {
      mergelines_node (node, total_lines, tfp, temp_output);
      queue_check_insert (queue, node);
      queue_check_insert_parent (queue, node);
      unlock_node (node);
    }

  if (node)
    {
      unlock_node (node);
      queue_insert (queue, node);
    }
}


static void sortlines (struct line *restrict, size_t, size_t,
                       struct merge_node *, struct merge_node_queue *,
                       FILE *, char const *);

/* Thread arguments for sortlines_thread. */

struct thread_args
{
  /* Source, i.e., the array of lines to sort.  This points just past
     the end of the array.  */
  struct line *lines;

  /* Number of threads to use.  If 0 or 1, sort single-threaded.  */
  size_t nthreads;

  /* Number of lines in LINES and DEST.  */
  size_t const total_lines;

  /* Merge node. Lines from this node and this node's sibling will merged
     to this node's parent. */
  struct merge_node *const node;

  /* The priority queue controlling available work for the entire
     internal sort.  */
  struct merge_node_queue *const queue;

  /* If at the top level, the file to output to, and the file's name.
     If the file is standard output, the file's name is null.  */
  FILE *tfp;
  char const *output_temp;
};

/* Like sortlines, except with a signature acceptable to pthread_create.  */

static void *
sortlines_thread (void *data)
{
  if (data)
    {
      const struct thread_args *args = data;
      sortlines (args->lines, args->nthreads, args->total_lines,
                 args->node, args->queue, args->tfp,
                 args->output_temp);
    }
  return NULL;
}

/* Sort lines, possibly in parallel.  The arguments are as in struct
   thread_args above.

   The algorithm has three phases: node creation, sequential sort,
   and binary merge.

   During node creation, sortlines recursively visits each node in the
   binary merge tree and creates a NODE structure corresponding to all the
   future line merging NODE is responsible for. For each call to
   sortlines, half the available threads are assigned to each recursive
   call, until a leaf node having only 1 available thread is reached.

   Each leaf node then performs two sequential sorts, one on each half of
   the lines it is responsible for. It records in its NODE structure that
   there are two sorted sublists available to merge from, and inserts its
   NODE into the priority queue.

   The binary merge phase then begins. Each thread drops into a loop
   where the thread retrieves a NODE from the priority queue, merges lines
   available to that NODE, and potentially insert NODE or its parent back
   into the queue if there are sufficient available lines for them to
   merge. This continues until all lines at all nodes of the merge tree
   have been merged. */

static void
sortlines (struct line *restrict lines, size_t nthreads,
           size_t total_lines, struct merge_node *node,
           struct merge_node_queue *queue, FILE *tfp, char const *temp_output)
{
  size_t nlines = node->nlo + node->nhi;

  bool const use_multithreading = (nthreads > 1)
                                  && (SUBTHREAD_LINES_HEURISTIC <= nlines);

  if (use_multithreading)
    {
      size_t lo_threads = nthreads / 2;
      size_t hi_threads = nthreads - lo_threads;
      pthread_t thread;
      struct thread_args args = {lines, lo_threads, total_lines,
                                 node->lo_child, queue, tfp, temp_output};

      if (pthread_create (&thread, NULL, sortlines_thread, &args) == 0)
        {
          sortlines (lines - node->nlo, hi_threads, total_lines,
                     node->hi_child, queue, tfp, temp_output);

          if (pthread_join (thread, NULL) != 0)
            {
              abort ();
            }
          return;
        }
    }

  size_t nlo = node->nlo;
  size_t nhi = node->nhi;
  struct line *temp = lines - total_lines;
  struct line *lines_hi = lines - nlo;

  if (1 < nhi)
    {
      sequential_sort (lines_hi, nhi, temp - nlo / 2, false);
    }
  if (1 < nlo)
    {
      sequential_sort (lines, nlo, temp, false);
    }

  node->lo = lines;
  node->hi = lines_hi;
  node->end_lo = lines_hi;
  node->end_hi = lines_hi - nhi;

  queue_insert (queue, node);
  merge_loop (queue, total_lines, tfp, temp_output);
}

/* Scan through FILES[NTEMPS .. NFILES-1] looking for files that are
   the same as OUTFILE.  If found, replace each with the same
   temporary copy that can be merged into OUTFILE without destroying
   OUTFILE before it is completely read.  This temporary copy does not
   count as a merge temp, so don't worry about incrementing NTEMPS in
   the caller; final cleanup will remove it, not zaptemp.

   This test ensures that an otherwise-erroneous use like
   "sort -m -o FILE ... FILE ..." copies FILE before writing to it.
   It's not clear that POSIX requires this nicety.
   Detect common error cases, but don't try to catch obscure cases like
   "cat ... FILE ... | sort -m -o FILE"
   where traditional "sort" doesn't copy the input and where
   people should know that they're getting into trouble anyway.
   Catching these obscure cases would slow down performance in
   common cases.  */

static bool
get_file_status (const char *name, bool is_stdin, struct stat *st)
{
  int ret = is_stdin ? fstat (STDIN_FILENO, st) : stat (name, st);
  return ret == 0;
}

static void
avoid_trashing_input (struct sortfile *files, size_t ntemps,
                      size_t nfiles, char const *outfile)
{
  struct tempnode *tempcopy = NULL;

  for (size_t i = ntemps; i < nfiles; i++)
    {
      bool is_stdin = STREQ (files[i].name, "-");
      bool same = false;

      if (outfile && !is_stdin && STREQ (outfile, files[i].name))
        {
          same = true;
        }
      else
        {
          struct stat *outst = get_outstatus ();
          if (!outst)
            {
              break;
            }

          struct stat instat;
          if (get_file_status (files[i].name, is_stdin, &instat))
            {
              same = psame_inode (&instat, outst);
            }
        }

      if (same)
        {
          if (!tempcopy)
            {
              FILE *tftp;
              tempcopy = create_temp (&tftp);
              if (!tempcopy)
                {
                  break;
                }
              mergefiles (&files[i], 0, 1, tftp, tempcopy->name);
            }

          files[i].name = tempcopy->name;
          files[i].temp = tempcopy;
        }
    }
}

/* Scan the input files to ensure all are accessible.
   Otherwise exit with a diagnostic.

   This will catch common issues with permissions etc.
   but will fail to notice issues where you can open but not read,
   like when a directory is specified on some systems.
   Catching these obscure cases could slow down performance in
   common cases.  */

static void
check_inputs (const char *const *files, size_t nfiles)
{
  for (size_t i = 0; i < nfiles; i++)
    {
      const char *current_file = files[i];
      if (STREQ (current_file, "-"))
        {
          continue;
        }

      if (euidaccess (current_file, R_OK) != 0)
        {
          sort_die (_("cannot read"), current_file);
        }
    }
}

/* Ensure a specified output file can be created or written to,
   and point stdout to it.  Do not truncate the file.
   Exit with a diagnostic on failure.  */

static void
check_output (char const *outfile)
{
  if (!outfile)
    {
      return;
    }

  int oflags = O_WRONLY | O_BINARY | O_CLOEXEC | O_CREAT;
  mode_t mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;

  int outfd = open (outfile, oflags, mode);
  if (outfd < 0)
    {
      sort_die (_("open failed"), outfile);
    }

  if (move_fd (outfd, STDOUT_FILENO) < 0)
    {
      sort_die (_("failed to redirect standard output"), outfile);
    }
}

/* Merge the input FILES.  NTEMPS is the number of files at the
   start of FILES that are temporary; it is zero at the top level.
   NFILES is the total number of files.  Put the output in
   OUTPUT_FILE; a null OUTPUT_FILE stands for standard output.  */

static void
perform_intermediate_merges (struct sortfile *files, size_t *ntemps_ptr,
                             size_t *nfiles_ptr)
{
  size_t ntemps = *ntemps_ptr;
  size_t nfiles = *nfiles_ptr;

  while (nfiles > nmerge)
    {
      size_t processed_count = 0;
      size_t new_file_count = 0;
      size_t temps_this_pass = ntemps;

      while (processed_count < nfiles)
        {
          size_t group_size = MIN (nmerge, nfiles - processed_count);
          if (group_size > 1)
            {
              FILE *tfp;
              struct tempnode *temp = create_temp (&tfp);
              size_t num_merged = mergefiles (&files[processed_count],
                                              MIN (temps_this_pass, group_size),
                                              group_size, tfp, temp->name);
              temps_this_pass -= MIN (temps_this_pass, num_merged);
              files[new_file_count].name = temp->name;
              files[new_file_count].temp = temp;
              new_file_count++;
              processed_count += group_size;
            }
          else
            {
              memmove (&files[new_file_count], &files[processed_count],
                       (nfiles - processed_count) * sizeof *files);
              new_file_count += nfiles - processed_count;
              break;
            }
        }
      nfiles = new_file_count;
      ntemps = temps_this_pass + new_file_count;
    }

  *ntemps_ptr = ntemps;
  *nfiles_ptr = nfiles;
}

static void
perform_final_merge (struct sortfile *files, size_t ntemps, size_t nfiles,
                     char const *output_file)
{
  while (true)
    {
      FILE **fps;
      size_t nopened = open_input_files (files, nfiles, &fps);

      if (nopened == nfiles)
        {
          FILE *ofp = stream_open (output_file, "w");
          if (ofp)
            {
              mergefps (files, ntemps, nfiles, ofp, output_file, fps);
              free (fps);
              return;
            }
          if (errno != EMFILE)
            sort_die (_("open failed"), output_file);

          for (size_t i = 0; i < nopened; i++)
            xfclose (fps[i], files[i].name);
          free (fps);
          nopened = 0;
        }

      if (nopened < 2)
        sort_die (_("open failed"), files[nopened].name);

      FILE *tfp = NULL;
      struct tempnode *temp = NULL;
      size_t merge_count = nopened;

      do
        {
          merge_count--;
          xfclose (fps[merge_count], files[merge_count].name);
          temp = maybe_create_temp (&tfp, merge_count < 2);
        }
      while (!temp);

      mergefps (files, MIN (ntemps, merge_count), merge_count, tfp,
                temp->name, fps);
      free (fps);

      ntemps -= MIN (ntemps, merge_count);
      files[0].name = temp->name;
      files[0].temp = temp;

      memmove (&files[1], &files[merge_count],
               (nfiles - merge_count) * sizeof *files);
      ntemps++;
      nfiles -= merge_count - 1;
    }
}

static void
merge (struct sortfile *files, size_t ntemps, size_t nfiles,
       char const *output_file)
{
  perform_intermediate_merges (files, &ntemps, &nfiles);
  avoid_trashing_input (files, ntemps, nfiles, output_file);
  perform_final_merge (files, ntemps, nfiles, output_file);
}

/* Sort NFILES FILES onto OUTPUT_FILE.  Use at most NTHREADS threads.  */

static size_t
get_bytes_per_line (size_t nthreads)
{
  if (nthreads > 1)
    {
      /* Calculate ceil(log2(nthreads)) for parallel sort merge width. */
      size_t log_p = 0;
      size_t temp = 1;
      while (temp < nthreads)
        {
          temp *= 2;
          log_p++;
        }
      return log_p * sizeof (struct line);
    }
  else
    {
      return sizeof (struct line) * 3 / 2;
    }
}

static void
sort_and_write_chunk (struct line *lines, size_t nlines, size_t nthreads,
                      FILE * out_fp, const char *out_name)
{
  if (nlines > 1)
    {
      struct merge_node_queue queue;
      queue_init (&queue, nthreads);
      struct merge_node *merge_tree =
        merge_tree_init (nthreads, nlines, lines);

      sortlines (lines, nthreads, nlines, merge_tree + 1, &queue, out_fp,
                 out_name);

      merge_tree_destroy (nthreads, merge_tree);
      queue_destroy (&queue);
    }
  else
    {
      write_unique (lines - 1, out_fp, out_name);
    }
}

static void
merge_temporary_files (size_t ntemps, const char *output_file)
{
  if (ntemps == 0)
    {
      return;
    }

  struct tempnode *node = temphead;
  struct sortfile *tempfiles = xnmalloc (ntemps, sizeof *tempfiles);
  for (size_t i = 0; i < ntemps; i++)
    {
      tempfiles[i].name = node->name;
      tempfiles[i].temp = node;
      node = node->next;
    }
  merge (tempfiles, ntemps, ntemps, output_file);
  free (tempfiles);
}

static void
sort (char *const *files, size_t nfiles, char const *output_file,
      size_t nthreads)
{
  struct buffer buf = { 0 };
  size_t ntemps = 0;
  bool finished_in_one_pass = false;
  const size_t bytes_per_line = get_bytes_per_line (nthreads);
  const size_t nfiles_original = nfiles;

  for (size_t i = 0; i < nfiles_original && !finished_in_one_pass; i++)
    {
      const char *file = files[i];
      FILE *fp = xfopen (file, "r");

      if (!buf.alloc)
        {
          initbuf (&buf, bytes_per_line,
                   sort_buffer_size (&fp, 1, files + i, nfiles - i,
                                     bytes_per_line));
        }
      buf.eof = false;

      while (fillbuf (&buf, fp, file))
        {
          bool can_concatenate =
            buf.eof && (i + 1 < nfiles_original)
            && (bytes_per_line + 1 <
                (buf.alloc - buf.used - bytes_per_line * buf.nlines));

          if (can_concatenate)
            {
              buf.left = buf.used;
              break;
            }

          saved_line.text = NULL;
          struct line *lines = buffer_linelim (&buf);
          FILE *out_fp;
          const char *out_name;

          bool is_last_chunk =
            buf.eof && (i + 1 == nfiles_original) && ntemps == 0 && !buf.left;

          if (is_last_chunk)
            {
              out_fp = xfopen (output_file, "w");
              out_name = output_file;
              finished_in_one_pass = true;
            }
          else
            {
              ntemps++;
              out_name = create_temp (&out_fp)->name;
            }

          sort_and_write_chunk (lines, buf.nlines, nthreads, out_fp,
                                out_name);
          xfclose (out_fp, out_name);

          if (finished_in_one_pass)
            {
              break;
            }
        }
      xfclose (fp, file);
    }

  free (buf.buf);

  if (!finished_in_one_pass)
    {
      merge_temporary_files (ntemps, output_file);
    }

  reap_all ();
}

/* Insert a malloc'd copy of key KEY_ARG at the end of the key list.  */

static void
insertkey (struct keyfield *key_arg)
{
  if (!key_arg)
    {
      return;
    }

  struct keyfield *key = xmemdup (key_arg, sizeof *key);
  key->next = nullptr;

  struct keyfield **p = &keylist;
  while (*p)
    {
      p = &(*p)->next;
    }
  *p = key;
}

/* Report a bad field specification SPEC, with extra info MSGID.  */

static void badfieldspec(const char *spec, const char *msgid)
{
    error(SORT_FAILURE, 0, _("%s: invalid field specification %s"),
          _(msgid), quote(spec));
}

/* Report incompatible options.  */

static void
incompatible_options (char const *opts)
{
  error (SORT_FAILURE, 0, _("options '-%s' are incompatible"), opts ? opts : "");
}

/* Check compatibility of ordering options.  */

static void
check_ordering_compatibility (void)
{
  struct keyfield *key;

  for (key = keylist; key; key = key->next)
    {
      int sort_option_count = key->numeric
                            + key->general_numeric
                            + key->human_numeric
                            + key->month
                            + (key->version || key->random || key->ignore);

      if (sort_option_count > 1)
        {
          char opts[sizeof short_options];
          struct keyfield temp_key = *key;

          temp_key.skipsblanks = false;
          temp_key.skipeblanks = false;
          temp_key.reverse = false;

          key_to_opts(&temp_key, opts);
          incompatible_options(opts);
        }
    }
}

/* Parse the leading integer in STRING and store the resulting value
   (which must fit into size_t) into *VAL.  Return the address of the
   suffix after the integer.  If the value is too large, silently
   substitute SIZE_MAX.  If MSGID is null, return nullptr after
   failure; otherwise, report MSGID and exit on failure.  */

static char const *
parse_field_count (char const *string, size_t *val, char const *msgid)
{
  char *suffix;
  uintmax_t n;
  enum strtol_error err = xstrtoumax (string, &suffix, 10, &n, "");

  if (err == LONGINT_INVALID)
    {
      if (msgid)
        error (SORT_FAILURE, 0, _("%s: invalid count at start of %s"),
               _(msgid), quote (string));
      return nullptr;
    }

  if ((err & LONGINT_OVERFLOW) || n > SIZE_MAX)
    {
      *val = SIZE_MAX;
    }
  else
    {
      *val = (size_t) n;
    }

  return suffix;
}

/* Handle interrupts and hangups. */

static void
sighandler(int sig)
{
  cleanup();
  signal(sig, SIG_DFL);
  raise(sig);
}

/* Set the ordering options for KEY specified in S.
   Return the address of the first character in S that
   is not a valid ordering option.
   BLANKTYPE is the kind of blanks that 'b' should skip. */

static char const *
set_ordering (char const *s, struct keyfield *key, enum blanktype blanktype)
{
  for (; *s; ++s)
    {
      switch (*s)
        {
        case 'b':
          if (blanktype == bl_start || blanktype == bl_both)
            key->skipsblanks = true;
          if (blanktype == bl_end || blanktype == bl_both)
            key->skipeblanks = true;
          break;
        case 'd':
          key->ignore = nondictionary;
          break;
        case 'f':
          key->translate = fold_toupper;
          break;
        case 'g':
          key->general_numeric = true;
          break;
        case 'h':
          key->human_numeric = true;
          break;
        case 'i':
          if (!key->ignore)
            key->ignore = nonprinting;
          break;
        case 'M':
          key->month = true;
          break;
        case 'n':
          key->numeric = true;
          break;
        case 'R':
          key->random = true;
          break;
        case 'r':
          key->reverse = true;
          break;
        case 'V':
          key->version = true;
          break;
        default:
          return s;
        }
    }
  return s;
}

/* Initialize KEY.  */

static struct keyfield *
key_init (struct keyfield *key)
{
  if (key)
    {
      memset (key, 0, sizeof *key);
      key->eword = SIZE_MAX;
    }
  return key;
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <locale.h>
#include <signal.h>
#include <getopt.h>
#include "system.h"
#include "sort.h"
#include "c-ctype.h"
#include "close-stream.h"
#include "exitfail.h"
#include "hard-locale.h"
#include "posixver.h"
#include "readtokens0.h"
#include "xmemcoll.h"
#include "gettext.h"
#define _(msgid) gettext (msgid)
#define N_(msgid) msgid

struct sort_opts
{
  struct keyfield gkey;
  bool gkey_only;
  char checkonly;
  bool mergeonly;
  char *random_source;
  size_t nthreads;
  size_t nfiles;
  bool posixly_correct;
  bool traditional_usage;
  char **files;
  char *files_from;
  const char *outfile;
};

static void
initialize_environment (int *argc, char ***argv)
{
  initialize_main (argc, argv);
  set_program_name ((*argv)[0]);
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);
  initialize_exit_failure (SORT_FAILURE);
  atexit (exit_cleanup);
}

static bool
initialize_locale_settings (void)
{
  bool locale_ok = !!setlocale (LC_ALL, "");
  hard_LC_COLLATE = hard_locale (LC_COLLATE);
#if HAVE_NL_LANGINFO
  hard_LC_TIME = hard_locale (LC_TIME);
#endif

  struct lconv const *locale = localeconv ();
  decimal_point = locale->decimal_point[0];
  if (!decimal_point || locale->decimal_point[1])
    decimal_point = '.';

  thousands_sep = locale->thousands_sep[0];
  if (thousands_sep && locale->thousands_sep[1])
    thousands_sep_ignored = true;
  if (!thousands_sep || locale->thousands_sep[1])
    thousands_sep = NON_CHAR;

  return locale_ok;
}

static void
initialize_signal_handlers (void)
{
  static int const sig[] = {
      SIGALRM, SIGHUP, SIGINT, SIGPIPE, SIGQUIT, SIGTERM,
#ifdef SIGPOLL
      SIGPOLL,
#endif
#ifdef SIGPROF
      SIGPROF,
#endif
#ifdef SIGVTALRM
      SIGVTALRM,
#endif
#ifdef SIGXCPU
      SIGXCPU,
#endif
#ifdef SIGXFSZ
      SIGXFSZ,
#endif
  };
  enum
  {
    nsigs = ARRAY_CARDINALITY (sig)
  };
  size_t i;

#if SA_NOCLDSTOP
  struct sigaction act;
  sigemptyset (&caught_signals);
  for (i = 0; i < nsigs; i++)
    {
      sigaction (sig[i], NULL, &act);
      if (act.sa_handler != SIG_IGN)
        sigaddset (&caught_signals, sig[i]);
    }

  act.sa_handler = sighandler;
  act.sa_mask = caught_signals;
  act.sa_flags = 0;

  for (i = 0; i < nsigs; i++)
    if (sigismember (&caught_signals, sig[i]))
      sigaction (sig[i], &act, NULL);
#else
  for (i = 0; i < nsigs; i++)
    if (signal (sig[i], SIG_IGN) != SIG_IGN)
      {
        signal (sig[i], sighandler);
        siginterrupt (sig[i], 1);
      }
#endif
  signal (SIGCHLD, SIG_DFL);
}

static bool
try_parse_traditional_key (const char *optarg, int argc, char **argv,
                           struct sort_opts *opts)
{
  if (optarg[0] != '+')
    return false;

  bool minus_pos_usage =
      (optind < argc && argv[optind][0] == '-' && c_isdigit (argv[optind][1]));
  opts->traditional_usage |= minus_pos_usage && !opts->posixly_correct;

  if (!opts->traditional_usage)
    return false;

  struct keyfield key_buf;
  struct keyfield *key = key_init (&key_buf);
  const char *s = parse_field_count (optarg + 1, &key->sword, NULL);
  if (s && *s == '.')
    s = parse_field_count (s + 1, &key->schar, NULL);
  if (!(key->sword || key->schar))
    key->sword = SIZE_MAX;

  if (!s || *set_ordering (s, key, bl_start))
    return false;

  if (minus_pos_usage)
    {
      const char *optarg1 = argv[optind++];
      s = parse_field_count (optarg1 + 1, &key->eword,
                             N_ ("invalid number after '-'"));
      if (*s == '.')
        s = parse_field_count (s + 1, &key->echar,
                               N_ ("invalid number after '.'"));
      if (!key->echar && key->eword)
        key->eword--;
      if (*set_ordering (s, key, bl_end))
        badfieldspec (optarg1, N_ ("stray character in field spec"));
    }
  key->traditional_used = true;
  insertkey (key);
  return true;
}

static void
set_global_ordering (int c, const char *optarg, struct keyfield *gkey)
{
  char str[2];
  if (c == SORT_OPTION)
    c = XARGMATCH ("--sort", optarg, sort_args, sort_types);
  str[0] = c;
  str[1] = '\0';
  set_ordering (str, gkey, bl_both);
}

static void
handle_check_option (int c, const char *optarg, char *checkonly)
{
  c = (optarg ? XARGMATCH ("--check", optarg, check_args, check_types) : c);
  if (*checkonly && *checkonly != c)
    incompatible_options ("cC");
  *checkonly = c;
}

static void
parse_key_option (const char *optarg)
{
  struct keyfield key_buf;
  struct keyfield *key = key_init (&key_buf);
  const char *s;

  s = parse_field_count (optarg, &key->sword, N_ ("invalid number at field start"));
  if (!key->sword--)
    badfieldspec (optarg, N_ ("field number is zero"));
  if (*s == '.')
    {
      s = parse_field_count (s + 1, &key->schar, N_ ("invalid number after '.'"));
      if (!key->schar--)
        badfieldspec (optarg, N_ ("character offset is zero"));
    }
  if (!(key->sword || key->schar))
    key->sword = SIZE_MAX;

  s = set_ordering (s, key, bl_start);

  if (*s != ',')
    {
      key->eword = SIZE_MAX;
      key->echar = 0;
    }
  else
    {
      s = parse_field_count (s + 1, &key->eword, N_ ("invalid number after ','"));
      if (!key->eword--)
        badfieldspec (optarg, N_ ("field number is zero"));
      if (*s == '.')
        s = parse_field_count (s + 1, &key->echar, N_ ("invalid number after '.'"));
      s = set_ordering (s, key, bl_end);
    }

  if (*s)
    badfieldspec (optarg, N_ ("stray character in field spec"));
  insertkey (key);
}

static void
parse_tab_option (const char *optarg)
{
  char newtab = optarg[0];
  if (!newtab)
    error (SORT_FAILURE, 0, _ ("empty tab"));
  if (optarg[1])
    {
      if (STREQ (optarg, "\\0"))
        newtab = '\0';
      else
        error (SORT_FAILURE, 0, _ ("multi-character tab %s"), quote (optarg));
    }
  if (tab != TAB_DEFAULT && tab != newtab)
    error (SORT_FAILURE, 0, _ ("incompatible tabs"));
  tab = newtab;
}

static void
handle_compat_y_option (char **argv, const char *optarg)
{
  if (optarg == argv[optind - 1])
    {
      const char *p;
      for (p = optarg; c_isdigit (*p); p++)
        continue;
      optind -= (*p != '\0');
    }
}

static void
parse_options (int argc, char **argv, struct sort_opts *opts)
{
  int c;

  while (true)
    {
      int oi = -1;
      bool stop_parsing = (optind < argc && posixly_correct && opts->nfiles > 0
                           && !(opts->traditional_usage && !opts->checkonly
                                && argv[optind][0] == '-' && argv[optind][1] == 'o'
                                && (argv[optind][2] || optind + 1 < argc)));

      if (stop_parsing)
        c = -1;
      else
        c = getopt_long (argc, argv, short_options, long_options, &oi);

      if (c == -1)
        {
          if (optind >= argc)
            break;
          opts->files[opts->nfiles++] = argv[optind++];
          continue;
        }

      switch (c)
        {
        case 1:
          if (!try_parse_traditional_key (optarg, argc, argv, opts))
            opts->files[opts->nfiles++] = optarg;
          break;

        case SORT_OPTION:
        case 'b': case 'd': case 'f': case 'g': case 'h':
        case 'i': case 'M': case 'n': case 'r': case 'R': case 'V':
          set_global_ordering (c, optarg, &opts->gkey);
          break;

        case CHECK_OPTION:
        case 'c': case 'C':
          handle_check_option (c, optarg, &opts->checkonly);
          break;

        case COMPRESS_PROGRAM_OPTION:
          if (compress_program && !STREQ (compress_program, optarg))
            error (SORT_FAILURE, 0, _ ("multiple compress programs specified"));
          compress_program = optarg;
          break;

        case DEBUG_PROGRAM_OPTION: debug = true; break;
        case FILES0_FROM_OPTION: opts->files_from = optarg; break;
        case 'k': parse_key_option (optarg); break;
        case 'm': opts->mergeonly = true; break;
        case 'o':
          if (opts->outfile && !STREQ (opts->outfile, optarg))
            error (SORT_FAILURE, 0, _ ("multiple output files specified"));
          opts->outfile = optarg;
          break;

        case 's': stable = true; break;
        case 'u': unique = true; break;
        case 'z': eolchar = 0; break;
        case 't': parse_tab_option (optarg); break;
        case 'T': add_temp_dir (optarg); break;
        case 'S': specify_sort_size (oi, c, optarg); break;
        case 'y': handle_compat_y_option (argv, optarg); break;

        case NMERGE_OPTION: specify_nmerge (oi, c, optarg); break;

        case RANDOM_SOURCE_OPTION:
          if (opts->random_source && !STREQ (opts->random_source, optarg))
            error (SORT_FAILURE, 0, _ ("multiple random sources specified"));
          opts->random_source = optarg;
          break;

        case PARALLEL_OPTION: opts->nthreads = specify_nthreads (oi, c, optarg); break;
        case_GETOPT_HELP_CHAR;
        case_GETOPT_VERSION_CHAR (PROGRAM_NAME, AUTHORS);
        default: usage (SORT_FAILURE);
        }
    }
}

static void
process_files_from (struct sort_opts *opts)
{
  if (!opts->files_from)
    return;

  if (opts->nfiles)
    {
      error (0, 0, _ ("extra operand %s"), quoteaf (opts->files[0]));
      fprintf (stderr, "%s\n", _ ("file operands cannot be combined with --files0-from"));
      usage (SORT_FAILURE);
    }

  FILE *stream = xfopen (opts->files_from, "r");
  struct Tokens tok;
  readtokens0_init (&tok);

  if (!readtokens0 (stream, &tok))
    error (SORT_FAILURE, 0, _ ("cannot read file names from %s"), quoteaf (opts->files_from));
  xfclose (stream, opts->files_from);

  if (!tok.n_tok)
    error (SORT_FAILURE, 0, _ ("no input from %s"), quoteaf (opts->files_from));

  free (opts->files);
  opts->files = tok.tok;
  opts->nfiles = tok.n_tok;

  for (size_t i = 0; i < opts->nfiles; i++)
    {
      if (STREQ (opts->files[i], "-"))
        error (SORT_FAILURE, 0, _ ("when reading file names from standard input, no file name of %s allowed"), quoteaf (opts->files[i]));
      else if (opts->files[i][0] == '\0')
        error (SORT_FAILURE, 0, _ ("%s:%lu: invalid zero-length file name"), quotef (opts->files_from), (unsigned long int) i + 1);
    }
}

static void
apply_global_key_options (struct sort_opts *opts, bool *need_random)
{
  for (struct keyfield *key = keylist; key; key = key->next)
    {
      if (default_key_compare (key) && !key->reverse)
        {
          key->ignore = opts->gkey.ignore;
          key->translate = opts->gkey.translate;
          key->skipsblanks = opts->gkey.skipsblanks;
          key->skipeblanks = opts->gkey.skipeblanks;
          key->month = opts->gkey.month;
          key->numeric = opts->gkey.numeric;
          key->general_numeric = opts->gkey.general_numeric;
          key->human_numeric = opts->gkey.human_numeric;
          key->version = opts->gkey.version;
          key->random = opts->gkey.random;
          key->reverse = opts->gkey.reverse;
        }
      *need_random |= key->random;
    }

  if (!keylist && !default_key_compare (&opts->gkey))
    {
      opts->gkey_only = true;
      insertkey (&opts->gkey);
      *need_random |= opts->gkey.random;
    }
}

static void
finalize_setup (struct sort_opts *opts, bool locale_ok, bool need_random)
{
  check_ordering_compatibility ();

  if (debug)
    {
      if (opts->checkonly || opts->outfile)
        {
          static char dbg_opts[] = "X --debug";
          dbg_opts[0] = (opts->checkonly ? opts->checkonly : 'o');
          incompatible_options (dbg_opts);
        }
      if (locale_ok && !setlocale (LC_COLLATE, ""))
        locale_ok = false;
      if (!locale_ok)
        error (0, 0, "%s", _ ("failed to set locale"));
      if (hard_LC_COLLATE)
        error (0, 0, _ ("text ordering performed using %s sorting rules"), quote (setlocale (LC_COLLATE, NULL)));
      else
        error (0, 0, "%s", _ ("text ordering performed using simple byte comparison"));
      key_warnings (&opts->gkey, opts->gkey_only);
    }

  reverse = opts->gkey.reverse;

  if (need_random)
    random_md5_state_init (opts->random_source);

  if (temp_dir_count == 0)
    add_temp_dir (getenv ("TMPDIR") ? getenv ("TMPDIR") : DEFAULT_TMPDIR);

  if (opts->nfiles == 0)
    {
      opts->nfiles = 1;
      free (opts->files);
      opts->files = xmalloc (sizeof *opts->files);
      *opts->files = (char *) "-";
    }

  if (sort_size > 0)
    sort_size = MAX (sort_size, MIN_SORT_SIZE);
}

static void
run_sort_or_merge (struct sort_opts *opts)
{
  if (opts->checkonly)
    {
      if (opts->nfiles > 1)
        error (SORT_FAILURE, 0, _ ("extra operand %s not allowed with -%c"), quoteaf (opts->files[1]), opts->checkonly);
      if (opts->outfile)
        {
          static char chk_opts[] = {0, 'o', 0};
          chk_opts[0] = opts->checkonly;
          incompatible_options (chk_opts);
        }
      exit (check (opts->files[0], opts->checkonly) ? EXIT_SUCCESS : SORT_OUT_OF_ORDER);
    }

  check_inputs (opts->files, opts->nfiles);
  check_output (opts->outfile);

  if (opts->mergeonly)
    {
      struct sortfile *sortfiles = xcalloc (opts->nfiles, sizeof *sortfiles);
      for (size_t i = 0; i < opts->nfiles; ++i)
        sortfiles[i].name = opts->files[i];
      merge (sortfiles, 0, opts->nfiles, opts->outfile);
    }
  else
    {
      if (!opts->nthreads)
        {
          unsigned long int np = num_processors (NPROC_CURRENT_OVERRIDABLE);
          opts->nthreads = MIN (np, DEFAULT_MAX_THREADS);
        }
      size_t nthreads_max = SIZE_MAX / (2 * sizeof (struct merge_node));
      opts->nthreads = MIN (opts->nthreads, nthreads_max);
      sort (opts->files, opts->nfiles, opts->outfile, opts->nthreads);
    }
}

int
main (int argc, char **argv)
{
  struct sort_opts opts = {
      .gkey_only = false,
      .checkonly = 0,
      .mergeonly = false,
      .random_source = NULL,
      .nthreads = 0,
      .nfiles = 0,
      .files_from = NULL,
      .outfile = NULL
  };
  bool need_random = false;
  
  initialize_environment (&argc, &argv);
  bool locale_ok = initialize_locale_settings ();

  inittables ();
  have_read_stdin = false;

  initialize_signal_handlers ();

  key_init (&opts.gkey);
  opts.gkey.sword = SIZE_MAX;
  opts.posixly_correct = (getenv ("POSIXLY_CORRECT") != NULL);
  int posix_ver = posix2_version ();
  opts.traditional_usage = !(200112 <= posix_ver && posix_ver < 200809);
  opts.files = xnmalloc (argc, sizeof *opts.files);

  parse_options (argc, argv, &opts);
  process_files_from (&opts);
  apply_global_key_options (&opts, &need_random);
  finalize_setup (&opts, locale_ok, need_random);
  run_sort_or_merge (&opts);

  if (have_read_stdin && fclose (stdin) == EOF)
    sort_die (_ ("close failed"), "-");

  main_exit (EXIT_SUCCESS);
}
