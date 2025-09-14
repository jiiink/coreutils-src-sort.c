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
  ignore_value (write (STDERR_FILENO, errstr, strlen (errstr)));

  if (errnum)
    {
      char errbuf[INT_BUFSIZE_BOUND (int)];
      char *p = inttostr (errnum, errbuf);
      ignore_value (write (STDERR_FILENO, ": errno ", sizeof(": errno ") - 1));
      ignore_value (write (STDERR_FILENO, p, strlen (p)));
    }

  ignore_value (write (STDERR_FILENO, "\n", sizeof("\n") - 1));

  _exit (SORT_FAILURE);
}

/* Report MESSAGE for FILE, then clean up and exit.
   If FILE is null, it represents standard output.  */

static void
sort_die (char const *message, char const *file)
{
  int saved_errno = errno;

  error (SORT_FAILURE, saved_errno, "%s: %s", message,
         quotef (file ? file : _("standard output")));
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    emit_try_help ();
  else
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
"), stdout );
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
  int result_code = pthread_sigmask (SIG_BLOCK, &caught_signals, &status->sigs);
  status->valid = (result_code == 0);
}

/* Leave a critical section.  */
static void
cs_leave (struct cs_status const *status)
{
  if (status == NULL)
    {
      return;
    }

  if (status->valid)
    {
      int result = pthread_sigmask (SIG_SETMASK, &status->sigs, nullptr);
      (void)result;
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
  if (tabsize == 0) {
    return 0;
  }

  struct tempnode const *node = (struct tempnode const *)entry;

  unsigned int pid_value = (unsigned int)node->pid;

  return pid_value % tabsize;
}

#include <stdbool.h>

static bool
proctab_comparator (void const *e1, void const *e2)
{
  if (e1 == NULL) {
    return e2 == NULL;
  }
  if (e2 == NULL) {
    return false;
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
  int status;
  pid_t cpid;

  if (pid > 0)
    {
      cpid = waitpid (pid, &status, 0);
    }
  else
    {
      cpid = waitpid (-1, &status, WNOHANG);
    }

  if (cpid < 0)
    {
      error (SORT_FAILURE, errno, _("waiting for %s [-d]"),
             quoteaf (compress_program));
    }
  else if (cpid > 0)
    {
      if (pid > 0 || delete_proc (cpid))
        {
          bool abnormal_termination = false;
          if (WIFEXITED (status))
            {
              if (WEXITSTATUS (status) != 0)
                {
                  abnormal_termination = true;
                }
            }
          else
            {
              abnormal_termination = true;
            }

          if (abnormal_termination)
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
register_proc (struct tempnode *temp)
{
  if (proctab == nullptr)
    {
      struct hashtable *new_proctab = hash_initialize(INIT_PROCTAB_SIZE, nullptr,
                                                      proctab_hasher,
                                                      proctab_comparator,
                                                      nullptr);
      if (new_proctab == nullptr)
        xalloc_die();

      proctab = new_proctab;
    }

  temp->state = UNREAPED;

  if (!hash_insert(proctab, temp))
    xalloc_die();
}

/* If PID is in the process table, remove it and return true.
   Otherwise, return false.  */

static bool
delete_proc (pid_t pid)
{
  struct tempnode test;

  memset(&test, 0, sizeof(struct tempnode));
  test.pid = pid;
  struct tempnode *node = hash_remove (proctab, &test);
  if (! node)
    return false;
  node->state = REAPED;
  return true;
}

/* Remove PID from the process table, and wait for it to exit if it
   hasn't already.  */

static void
wait_proc (pid_t pid)
{
  if (delete_proc(pid)) {
    reap(pid);
  }
}

/* Reap any exited children.  Do not block; reap only those that have
   already exited.  */

static void
reap_exited (void)
{
  int reap_status;

  while (0 < nprocs)
  {
    reap_status = reap(0);

    if (reap_status > 0)
    {
      // A child process was successfully reaped. Continue checking for more.
    }
    else
    {
      // No child processes were ready (reap_status == 0) or an error occurred (reap_status == -1).
      // In either case, we should stop attempting to reap in this cycle.
      if (reap_status == 0 || errno == ECHILD)
      {
        // No child processes were ready to be reaped (WNOHANG condition)
        // or no more child processes exist (ECHILD).
        // This is a normal termination condition for this reaping loop.
        break;
      }
      else
      {
        // A genuine error occurred during reaping (e.g., EINTR, EINVAL).
        // The original code would have continued attempting to reap,
        // which is a reliability issue. Breaking here prevents an infinite loop on persistent errors.
        break;
      }
    }
  }
}

/* Reap at least one exited child, waiting if necessary.  */

#define REAP_ALL_CHILDREN_PROCESSES -1

static void
reap_some (void)
{
  reap(REAP_ALL_CHILDREN_PROCESSES);
  reap_exited();
}

/* Reap all children, waiting if necessary.  */

static void
reap_all (void)
{
  while (nprocs > 0)
    reap (-1);
}

/* Clean up any remaining temporary files.  */

static void
cleanup (void)
{
  struct tempnode const *current_node;
  struct tempnode const *next_node;

  current_node = temphead;
  while (current_node != nullptr)
    {
      next_node = current_node->next;
      unlink (current_node->name);
      free ((void *)current_node);
      current_node = next_node;
    }
  temphead = nullptr;
}

/* Cleanup actions to take when exiting.  */

static void
exit_cleanup (void)
{
  if (temphead != NULL)
    {
      struct cs_status cs;
      cs_enter (&cs);
      cleanup ();
      cs_leave (&cs);
    }

  close_stdout ();
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
  int fd;
  int saved_errno;
  char const *current_temp_dir;
  struct tempnode *node;
  char *file;
  size_t len;
  struct cs_status cs;

  cs_enter (&cs);
  {
    current_temp_dir = temp_dirs[temp_dir_index];

    if (++temp_dir_index == temp_dir_count)
      temp_dir_index = 0;

    len = strlen (current_temp_dir);
    node = xmalloc (FLEXSIZEOF (struct tempnode, name, len + sizeof slashbase));
    file = node->name;

    memcpy (file, current_temp_dir, len);
    memcpy (file + len, slashbase, sizeof slashbase);
    node->next = nullptr;

    fd = mkostemp (file, O_CLOEXEC);

    if (0 <= fd)
      {
        *temptail = node;
        temptail = &node->next;
      }
    saved_errno = errno;
  }
  cs_leave (&cs);
  errno = saved_errno;

  if (fd < 0)
    {
      if (! (survive_fd_exhaustion && errno == EMFILE))
        error (SORT_FAILURE, errno, _("cannot create temporary file in %s"),
               quoteaf (current_temp_dir));
      free (node);
      node = nullptr;
    }

  *pfd = fd;
  return node;
}

/* Return a pointer to stdout status, or nullptr on failure.  */

static struct stat *
get_outstatus (void)
{
  static bool s_initialized = false;
  static int s_fstat_error = 0; /* 0 for success, positive for errno on failure */
  static struct stat s_outstat;

  if (!s_initialized)
    {
      if (fstat (STDOUT_FILENO, &s_outstat) == 0)
        {
          s_fstat_error = 0; /* Success */
        }
      else
        {
          s_fstat_error = errno; /* Capture the error code */
        }
      s_initialized = true; /* Mark as initialized */
    }

  return s_fstat_error == 0 ? &s_outstat : NULL;
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
          if (fd < 0)
            {
              return NULL;
            }
          
          fp = fdopen (fd, how);
          if (fp == NULL)
            {
              close(fd);
              return NULL;
            }
        }
      
      if (fp != NULL)
        {
          fadvise (fp, FADVISE_SEQUENTIAL);
        }
    }
  else if (*how == 'w')
    {
      if (file != NULL)
        {
          if (ftruncate (STDOUT_FILENO, 0) != 0)
            {
              int ftruncate_errno = errno;
              struct stat *outst = get_outstatus ();

              if (outst == NULL || S_ISREG (outst->st_mode) || S_TYPEISSHM (outst))
                {
                  error (SORT_FAILURE, ftruncate_errno, _("%s: error truncating"),
                         quotef (file));
                }
            }
        }
      fp = stdout;
    }
  else
    affirm (!"unexpected mode passed to stream_open");

  return fp;
}

/* Same as stream_open, except always return a non-null value; die on
   failure.  */

static FILE *
xfopen (char const *file, char const *how)
{
  FILE *fp = stream_open (file, how);

  if (fp == NULL) {
    sort_die (_("open failed"), file);
  }

  return fp;
}

/* Close FP, whose name is FILE, and report any errors.  */

static void
xfclose (FILE *fp, char const *file)
{
  if (fp == stdin)
    {
      clearerr (fp);
    }
  else if (fp == stdout)
    {
      if (fflush (fp) != 0)
        sort_die (_("fflush failed"), file);
    }
  else
    {
      if (fclose (fp) != 0)
        sort_die (_("close failed"), file);
    }
}

/* Move OLDFD to NEWFD.  If OLDFD != NEWFD, NEWFD is not close-on-exec.  */

static int
move_fd (int oldfd, int newfd)
{
  if (oldfd == newfd)
    {
      return 0;
    }

  if (dup2(oldfd, newfd) == -1)
    {
      return -1;
    }

  if (close(oldfd) == -1)
    {
      return -1;
    }

  return 0;
}

/* Fork a child process for piping to and do common cleanup.  The
   TRIES parameter specifies how many times to try to fork before
   giving up.  Return the PID of the child, or -1 (setting errno)
   on failure. */

static pid_t
pipe_fork (int pipefds[2], size_t num_fork_attempts)
{
#if HAVE_WORKING_FORK
  struct tempnode *previous_temphead;
  int saved_errno_val;
  double retry_wait_seconds = 0.25;
  pid_t child_pid;
  struct cs_status critical_section_status;

  if (pipe2 (pipefds, O_CLOEXEC) < 0)
    return -1;

  if (nmerge + 1 < nprocs)
    reap_some ();

  while (num_fork_attempts--)
    {
      cs_enter (&critical_section_status);
      previous_temphead = temphead;
      temphead = nullptr;

      child_pid = fork ();
      saved_errno_val = errno;
      if (child_pid) /* Parent process */
        temphead = previous_temphead;

      cs_leave (&critical_section_status);
      errno = saved_errno_val;

      if (0 <= child_pid || errno != EAGAIN)
        break;
      else
        {
          xnanosleep (retry_wait_seconds);
          retry_wait_seconds *= 2;
          reap_exited ();
        }
    }

  if (child_pid < 0)
    {
      saved_errno_val = errno; /* Save errno again before closing FDs */
      close (pipefds[0]);
      close (pipefds[1]);
      errno = saved_errno_val; /* Restore errno after closing FDs */
    }
  else if (child_pid == 0) /* Child process */
    {
      close (STDIN_FILENO);
      close (STDOUT_FILENO);
    }
  else /* Parent process, child_pid > 0 */
    ++nprocs;

  return child_pid;

#else  /* ! HAVE_WORKING_FORK */
  return -1;
#endif
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return
   the address of the new temp node.  If the creation
   fails, return nullptr if the failure is due to file descriptor
   exhaustion and SURVIVE_FD_EXHAUSTION; otherwise, die.  */

static struct tempnode *
maybe_create_temp (FILE **pfp, bool survive_fd_exhaustion)
{
  int tempfd;
  struct tempnode *node = create_temp_file (&tempfd, survive_fd_exhaustion);
  if (!node)
    return nullptr;

  node->state = UNCOMPRESSED;

  if (compress_program)
    {
      int pipefds[2];
      pid_t child_pid;

      child_pid = pipe_fork (pipefds, MAX_FORK_TRIES_COMPRESS);

      if (child_pid < 0)
        {
          close(tempfd);
          destroy_temp_file(node);
          return nullptr;
        }
      else if (child_pid == 0)
        {
          close(pipefds[1]);

          if (move_fd (tempfd, STDOUT_FILENO) == -1)
            async_safe_die (errno, "child: couldn't move tempfd to STDOUT_FILENO");

          if (move_fd (pipefds[0], STDIN_FILENO) == -1)
            async_safe_die (errno, "child: couldn't move pipefds[0] to STDIN_FILENO");

          execlp (compress_program, compress_program, (char *) nullptr);

          async_safe_die (errno, "child: couldn't execute compress program");
        }
      else
        {
          close(tempfd);
          close(pipefds[0]);
          tempfd = pipefds[1];

          register_proc (node);
        }
    }

  *pfp = fdopen (tempfd, "w");
  if (! *pfp)
    {
      int saved_errno = errno;
      close(tempfd);
      destroy_temp_file(node);
      errno = saved_errno;
      sort_die (_("couldn't create temporary file"), node->name);
    }

  return node;
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return the address
   of the new temp node.  Die on failure.  */

static const bool TEMP_NODE_NON_EXCLUSIVE_MODE = false;

static struct tempnode *
create_temp (FILE **pfp)
{
  return maybe_create_temp (pfp, TEMP_NODE_NON_EXCLUSIVE_MODE);
}

/* Open a compressed temp file and start a decompression process through
   which to filter the input.  Return nullptr (setting errno to
   EMFILE) if we ran out of file descriptors, and die on any other
   kind of failure.  */

static FILE *
open_temp (struct tempnode *temp)
{
  int tempfd = -1;
  int pipefds[2] = {-1, -1};
  FILE *fp = nullptr;
  pid_t child_pid = -1;

  if (temp->state == UNREAPED)
    wait_proc (temp->pid);

  tempfd = open (temp->name, O_RDONLY);
  if (tempfd < 0)
    {
      return nullptr;
    }

  child_pid = pipe_fork (pipefds, MAX_FORK_TRIES_DECOMPRESS);

  switch (child_pid)
    {
    case -1:
      // pipe_fork failed.
      // As per original logic, only report if error is not EMFILE,
      // then force errno to EMFILE for the caller.
      if (errno != EMFILE)
        error (SORT_FAILURE, errno, _("couldn't create process for %s -d"),
               quoteaf (compress_program));

      // Clean up resources in the parent's error path.
      close (tempfd);
      // pipefds were not successfully created or are invalid here, no need to close them.

      errno = EMFILE; // Propagate EMFILE as the specific error for this function.
      return nullptr;

    case 0:
      // Child process.
      // Being the child of a multithreaded program before exec,
      // we're restricted to calling async-signal-safe routines here.

      // Close the read end of the pipe in the child.
      close (pipefds[0]);

      // Redirect tempfd to STDIN and pipefds[1] to STDOUT.
      move_fd (tempfd, STDIN_FILENO);
      move_fd (pipefds[1], STDOUT_FILENO);

      // Execute the compression program.
      execlp (compress_program, compress_program, "-d", (char *) nullptr);

      // If execlp fails, terminate the child process safely.
      async_safe_die (errno, "couldn't execute compress program (with -d)");

      // This line should ideally not be reached if async_safe_die terminates the process.
      // Included for extreme robustness as a fallback.
      _exit(127);

    default:
      // Parent process.
      temp->pid = child_pid;
      register_proc (temp);

      // Parent no longer needs its copy of tempfd or the write end of the pipe.
      close (tempfd);
      close (pipefds[1]);

      // Open a FILE stream for the read end of the pipe.
      fp = fdopen (pipefds[0], "r");
      if (! fp)
        {
          // fdopen failed. Capture errno before closing the descriptor.
          int saved_errno = errno;
          close (pipefds[0]); // Close the pipe read end if fdopen failed.
          errno = saved_errno; // Restore errno for the caller.
        }
      // If fdopen succeeded, pipefds[0] is now owned by fp and will be closed by fclose.
      break;
    }

  return fp;
}

/* Append DIR to the array of temporary directory names.  */
static char const **temp_dirs = NULL;
static size_t temp_dir_count = 0;
static size_t temp_dir_alloc = 0;

/* These constants replace magic numbers used in the xpalloc function call.
 * Their specific meaning is determined by the xpalloc implementation.
 * XPALLOC_MIN_GROWTH_INCREMENT typically ensures space for at least one more element.
 * XPALLOC_DEFAULT_GROWTH_STRATEGY could be a flag for xpalloc to use its default
 * internal growth mechanism (e.g., doubling capacity).
 */
static const size_t XPALLOC_MIN_GROWTH_INCREMENT = 1;
static const int XPALLOC_DEFAULT_GROWTH_STRATEGY = -1;

/* Forward declaration for xpalloc, assuming it's defined elsewhere.
 * The signature is inferred from its usage in the original code.
 */
extern void *xpalloc(void *ptr, size_t *allocated_count, size_t min_growth_amount, int strategy_flags, size_t element_size);

static void
add_temp_dir (char const *dir)
{
  if (temp_dir_count == temp_dir_alloc)
    {
      /* Reallocate temp_dirs to increase capacity.
       * xpalloc is assumed to handle memory allocation, potential errors (e.g., exiting on failure),
       * and updating temp_dir_alloc to the new capacity.
       * An explicit cast is used for clarity and type safety.
       */
      temp_dirs = (char const **) xpalloc(temp_dirs, &temp_dir_alloc,
                                          XPALLOC_MIN_GROWTH_INCREMENT,
                                          XPALLOC_DEFAULT_GROWTH_STRATEGY,
                                          sizeof *temp_dirs);
    }

  /* Assign the directory string pointer to the next available slot
   * and then increment the count of stored directories.
   */
  temp_dirs[temp_dir_count++] = dir;
}

/* Remove NAME from the list of temporary files.  */

static void
zaptemp (char const *name)
{
  struct tempnode *volatile *pnode;
  struct tempnode *node;

  for (pnode = &temphead; (node = *pnode) != NULL; pnode = &node->next)
    if (node->name == name)
      break;

  if (node == NULL)
    return;

  if (node->state == UNREAPED)
    wait_proc (node->pid);

  struct tempnode *next_node = node->next;
  struct cs_status cs;
  int unlink_status;
  int unlink_errno = 0;

  cs_enter (&cs);
  unlink_status = unlink (name);
  unlink_errno = errno;
  *pnode = next_node;
  cs_leave (&cs);

  if (unlink_status != 0)
    error (0, unlink_errno, _("warning: cannot remove: %s"), quotef (name));

  if (next_node == NULL)
    temptail = pnode;

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
process_month_name_entry(struct month *month_entry, const char *src_name_str, size_t month_index)
{
  size_t s_len = strlen(src_name_str);
  char *name = malloc(s_len + 1);
  if (name == NULL)
    {
      // In a real application, consider a more graceful error handling
      // like logging and then terminating, or returning an error if possible.
      // For a void function called during critical initialization, aborting is a robust choice.
      abort();
    }

  month_entry->name = name;
  month_entry->val = (int)month_index + 1;

  size_t k = 0;
  for (size_t j = 0; j < s_len; j++)
    {
      // Ensure char is treated as unsigned char for ctype functions and array indexing
      unsigned char uc = (unsigned char)src_name_str[j];
      if (!isblank(uc))
        {
          name[k++] = fold_toupper[uc];
        }
    }
  name[k] = '\0';
}

static void
inittables (void)
{
  size_t i;

  for (i = 0; i < UCHAR_LIM; ++i)
    {
      // 'i' is size_t, already non-negative and within [0, UCHAR_LIM-1],
      // so direct use with ctype functions is safe and standard.
      blanks[i] = i == '\n' || isblank (i);
      nondictionary[i] = ! blanks[i] && ! isalnum (i);
      nonprinting[i] = ! isprint (i);
      fold_toupper[i] = toupper (i);
    }

#if HAVE_NL_LANGINFO
  if (hard_LC_TIME)
    {
      for (i = 0; i < MONTHS_PER_YEAR; i++)
        {
          char const *s = nl_langinfo (ABMON_1 + i);
          process_month_name_entry(&monthtab[i], s, i);
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
  uintmax_t parsed_val;
  struct rlimit rlimit_info;
  enum strtol_error parse_error = xstrtoumax (s, nullptr, 10, &parsed_val, "");

  unsigned int max_nmerge_allowed;
  rlim_t rlim_cur_val;

  if (getrlimit (RLIMIT_NOFILE, &rlimit_info) == 0)
    rlim_cur_val = rlimit_info.rlim_cur;
  else
    rlim_cur_val = OPEN_MAX;

  if (rlim_cur_val < 3)
    max_nmerge_allowed = 0;
  else
    {
      uintmax_t temp_max_fds = rlim_cur_val - 3;
      if (temp_max_fds > UINT_MAX)
        max_nmerge_allowed = UINT_MAX;
      else
        max_nmerge_allowed = (unsigned int)temp_max_fds;
    }

  if (parse_error != LONGINT_OK)
    {
      if (parse_error == LONGINT_OVERFLOW)
        {
          error (0, 0, _("--%s argument %s too large"),
                 long_options[oi].name, quote (s));
          error (SORT_FAILURE, 0,
                 _("maximum --%s argument with current rlimit is %u"),
                 long_options[oi].name, max_nmerge_allowed);
        }
      else
        {
          xstrtol_fatal (parse_error, oi, c, long_options, s);
        }
      return;
    }

  if (parsed_val > UINT_MAX)
    {
      error (0, 0, _("--%s argument %s too large"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("maximum --%s argument with current rlimit is %u"),
             long_options[oi].name, max_nmerge_allowed);
      return;
    }

  unsigned int candidate_nmerge = (unsigned int)parsed_val;

  if (candidate_nmerge < 2)
    {
      error (0, 0, _("invalid --%s argument %s"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("minimum --%s argument is %s"),
             long_options[oi].name, quote ("2"));
      return;
    }
  else if (candidate_nmerge > max_nmerge_allowed)
    {
      error (0, 0, _("--%s argument %s too large"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("maximum --%s argument with current rlimit is %u"),
             long_options[oi].name, max_nmerge_allowed);
      return;
    }

  nmerge = candidate_nmerge;
}

/* Specify the amount of main memory to use when sorting.  */
static void
specify_sort_size (int oi, char c, char const *s)
{
  uintmax_t n;
  char *suffix;
  
  // To correctly identify if xstrtoumax *itself* consumed a standard unit (e.g., 'K', 'M'),
  // we first find the end of the numeric part without any units.
  // We use a temporary pointer to track this, without modifying 'n' yet with units.
  char *numeric_end_without_units;
  (void) xstrtoumax(s, &numeric_end_without_units, 10, &n, ""); // Parse only number, get pointer to first non-digit

  // Now, parse the input string with full unit support, including standard units.
  // This call will set 'n' to the final value after applying 'K', 'M', etc., if present.
  enum strtol_error e = xstrtoumax (s, &suffix, 10, &n, "EgGkKmMPQRtTYZ");

  // Determine if xstrtoumax successfully processed and consumed a standard unit.
  // This is true if parsing with no units stopped *before* the final suffix,
  // AND parsing with units resulted in the suffix being at the end of the string (meaning a unit was consumed).
  bool xstrtoumax_handled_standard_unit = (e == LONGINT_OK && *suffix == '\0' && *numeric_end_without_units != '\0');

  // The default unit is KiB. Apply it only if parsing was successful and
  // no standard unit was explicitly specified and handled by xstrtoumax.
  if (e == LONGINT_OK && !xstrtoumax_handled_standard_unit && *suffix == '\0')
    {
      if (n > UINTMAX_MAX / 1024)
        e = LONGINT_OVERFLOW;
      else
        n *= 1024;
    }

  // Handle 'b' (bytes) and '%' (percent of memory) suffixes.
  // This block is entered if xstrtoumax detected an invalid suffix char
  // (because 'b' and '%' are not in "EgGkKmMPQRtTYZ") and it's a single character.
  if (e == LONGINT_INVALID_SUFFIX_CHAR && *suffix != '\0' && !suffix[1])
    {
      switch (suffix[0])
        {
        case 'b':
          // 'b' means bytes, which 'n' already represents. Parsing is considered OK.
          e = LONGINT_OK;
          break;

        case '%':
          {
            // Calculate percentage of total physical memory.
            double mem = physmem_total () * n / 100.0; // Use 100.0 for floating-point division

            // Check for overflow against UINTMAX_MAX.
            if (mem < (double)UINTMAX_MAX)
              {
                n = (uintmax_t)mem; // Truncate to uintmax_t as per original behavior
                e = LONGINT_OK;
              }
            else
              e = LONGINT_OVERFLOW;
          }
          break;
        // If it's another single invalid character, 'e' remains LONGINT_INVALID_SUFFIX_CHAR.
        // This leads to xstrtol_fatal at the end, matching the original behavior.
        }
    }

  // Final check for successful parsing and updating the global 'sort_size'.
  if (e == LONGINT_OK)
    {
      // If multiple sort sizes are specified, take the maximum, so option order does not matter.
      if (n < sort_size)
        return; // Current 'n' is not larger than existing 'sort_size', so no update needed.

      sort_size = n;
      // The original `if (sort_size == n)` check was redundant for same-type assignment
      // and has been removed for improved maintainability. Overflow should be caught earlier.
      sort_size = MAX (sort_size, MIN_SORT_SIZE);
      return;
    }

  // If we reach here, an error occurred during parsing or unit processing.
  xstrtol_fatal (e, oi, c, long_options, s);
}

/* Specify the number of threads to spawn during internal sort.  */
static size_t
specify_nthreads (int oi, char c, char const *s)
{
  uintmax_t parsed_nthreads_umax;
  enum strtol_error e = xstrtoumax (s, NULL, 10, &parsed_nthreads_umax, "");

  if (e == LONGINT_OVERFLOW)
    return SIZE_MAX;

  if (e != LONGINT_OK)
    xstrtol_fatal (e, oi, c, long_options, s);

  size_t final_nthreads;

  // Clamp the parsed value to fit within the maximum representable value of size_t.
  // This handles cases where uintmax_t is wider than size_t and the parsed value
  // exceeds SIZE_MAX.
  if (parsed_nthreads_umax > SIZE_MAX)
    final_nthreads = SIZE_MAX;
  else
    final_nthreads = (size_t) parsed_nthreads_umax; // Safe cast as value is guaranteed to fit.

  // Validate that the number of threads must be nonzero, which is an application-specific requirement.
  if (final_nthreads == 0)
    error (SORT_FAILURE, 0, _("number in parallel must be nonzero"));

  return final_nthreads;
}

/* Return the default sort size.  */
#include <sys/resource.h>
#include <stddef.h>
#include <limits.h>

static inline size_t min_sz(size_t a, size_t b) {
    return a < b ? a : b;
}

static inline size_t max_sz(size_t a, size_t b) {
    return a > b ? a : b;
}

static inline size_t convert_rlim_to_size_t(rlim_t val) {
    if (val == RLIM_INFINITY) {
        return SIZE_MAX;
    }
    if ((sizeof(rlim_t) > sizeof(size_t)) && (val > SIZE_MAX)) {
        return SIZE_MAX;
    }
    return (size_t)val;
}

static inline size_t convert_double_to_size_t_clamped(double val) {
    if (val <= 0.0) {
        return 0;
    }
    if (val >= (double)SIZE_MAX) {
        return SIZE_MAX;
    }
    return (size_t)val;
}

static size_t
default_sort_size (void)
{
  size_t size = SIZE_MAX;
  struct rlimit rlimit_info;

  if (getrlimit(RLIMIT_DATA, &rlimit_info) == 0) {
    size = min_sz(size, convert_rlim_to_size_t(rlimit_info.rlim_cur));
  }

#ifdef RLIMIT_AS
  if (getrlimit(RLIMIT_AS, &rlimit_info) == 0) {
    size = min_sz(size, convert_rlim_to_size_t(rlimit_info.rlim_cur));
  }
#endif

  size /= 2;

#ifdef RLIMIT_RSS
  if (getrlimit(RLIMIT_RSS, &rlimit_info) == 0) {
    size_t rss_limit = convert_rlim_to_size_t(rlimit_info.rlim_cur);
    rss_limit = (rss_limit / 16) * 15;
    size = min_sz(size, rss_limit);
  }
#endif

  double avail_mem_raw = physmem_available();
  double total_mem_raw = physmem_total();

  double mem_candidate_double = total_mem_raw / 8.0;
  if (avail_mem_raw > mem_candidate_double) {
      mem_candidate_double = avail_mem_raw;
  }

  size = min_sz(size, convert_double_to_size_t_clamped(total_mem_raw * 0.75));

  size = min_sz(size, convert_double_to_size_t_clamped(mem_candidate_double));

  return max_sz(size, MIN_SORT_SIZE);
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
  // Determine the effective size bound based on user input or default.
  // This replaces the problematic 'static size_t size_bound;', making the
  // function stateless and easier to reason about.
  size_t effective_size_bound = sort_size;
  if (effective_size_bound == 0)
    {
      effective_size_bound = default_sort_size();
    }
  
  // A bound on the number of bytes per input line (including newline) plus an extra byte.
  // This calculation must not overflow. line_bytes is size_t.
  // original: worst_case_per_input_byte = line_bytes + 1;
  size_t worst_case_per_input_byte;
  if (line_bytes > SIZE_MAX - 1)
    {
      // If line_bytes is so large that adding 1 would overflow size_t,
      // it implies an extremely large line, effectively hitting the limit.
      return effective_size_bound;
    }
  worst_case_per_input_byte = line_bytes + 1;

  // Initialize total 'size' with room for one extra input line and an extra byte.
  // This is equivalent to `worst_case_per_input_byte + 1`.
  size_t size;
  if (worst_case_per_input_byte > SIZE_MAX - 1)
    {
      // If worst_case_per_input_byte itself is near SIZE_MAX, adding 1 would overflow.
      return effective_size_bound;
    }
  size = worst_case_per_input_byte + 1;

  // Initial check: if the base size already exceeds the bound, return the bound.
  if (size > effective_size_bound)
    {
      return effective_size_bound;
    }

  for (size_t i = 0; i < nfiles; i++)
    {
      struct stat st;
      int stat_ret;
      const char *current_filename = files[i];

      // Decompose complex ternary operator for clarity and maintainability.
      if (i < nfps)
        {
          stat_ret = fstat (fileno (fps[i]), &st);
        }
      else if (STREQ (current_filename, "-"))
        {
          stat_ret = fstat (STDIN_FILENO, &st);
        }
      else
        {
          stat_ret = stat (current_filename, &st);
        }

      if (stat_ret != 0)
        sort_die (_("stat failed"), current_filename);

      size_t current_file_size; // Use size_t for file size after validation
      if (usable_st_size (&st) && 0 < st.st_size)
        {
          // Ensure st.st_size (off_t) can be safely converted to size_t.
          // off_t can be signed and potentially larger than size_t.
          if (st.st_size < 0 || st.st_size > (off_t)SIZE_MAX)
            {
              // If the file size is negative (error/special) or too large to fit in size_t,
              // it's an effectively unbounded or error condition for buffer allocation.
              // Return the effective_size_bound as a safety limit.
              return effective_size_bound;
            }
          current_file_size = (size_t)st.st_size;
        }
      else
        {
          // The file has unknown size. Use user-specified sort_size or guess.
          // If sort_size is non-zero, it means a hard limit was provided,
          // and we should respect that by returning it immediately.
          if (sort_size > 0)
            return sort_size;
          current_file_size = INPUT_FILE_SIZE_GUESS;
        }
      
      // Add the amount of memory needed to represent the worst case for this file.
      // This is current_file_size * worst_case_per_input_byte + 1.
      // Perform robust overflow checks before multiplication and addition.

      // Check for current_file_size * worst_case_per_input_byte overflow.
      // `worst_case_per_input_byte` is guaranteed to be at least 1.
      if (current_file_size > 0 && worst_case_per_input_byte > SIZE_MAX / current_file_size)
        {
          // Multiplication would overflow, so the total size will definitely exceed any reasonable bound.
          return effective_size_bound;
        }
      
      size_t current_file_worst_case = current_file_size * worst_case_per_input_byte;

      // Check for current_file_worst_case + 1 overflow.
      if (current_file_worst_case == SIZE_MAX)
        {
          // Adding 1 would overflow size_t.
          return effective_size_bound;
        }
      current_file_worst_case += 1;

      // Check if adding 'current_file_worst_case' to 'size' would exceed 'effective_size_bound'
      // or if the addition itself would overflow size_t.
      // This combined check is robust against both exceeding the bound and intermediate overflow.
      if (current_file_worst_case > effective_size_bound ||
          size > effective_size_bound - current_file_worst_case)
        {
          return effective_size_bound;
        }
      size += current_file_worst_case;
    }

  return size;
}

/* Initialize BUF.  Reserve LINE_BYTES bytes for each line; LINE_BYTES
   must be at least sizeof (struct line).  Allocate ALLOC bytes
   initially.  */

static void
initbuf (struct buffer *buf, size_t line_bytes, size_t alloc)
{
  while (true)
    {
      size_t alignment = sizeof(struct line);
      size_t remainder = alloc % alignment;

      if (remainder == 0)
        {
          alloc += alignment;
        }
      else
        {
          alloc += alignment - remainder;
        }

      buf->buf = malloc (alloc);
      if (buf->buf)
        break;
      
      alloc /= 2;
      if (alloc <= line_bytes + 1)
        xalloc_die ();
    }

  buf->line_bytes = line_bytes;
  buf->alloc = alloc;
  buf->used = buf->left = buf->nlines = 0;
  buf->eof = false;
}

/* Return one past the limit of the line array.  */

static inline struct line *
buffer_linelim (struct buffer const *buf)
{
  return (struct line *)((char *)buf->buf + buf->alloc);
}

/* Return a pointer to the first character of the field specified
   by KEY in LINE. */

static char *
begfield (struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text;
  // `end_ptr` points one past the last character of the line.
  // This is the standard C way to define a buffer's end for iteration: [start, end_ptr).
  char *const end_ptr = ptr + line->length;

  // Use local copies for loop counters to avoid modifying the input `key` struct.
  size_t current_sword = key->sword;
  size_t schar_offset = key->schar;

  // If `line->length` is 0, `end_ptr` will be equal to `ptr`,
  // causing all `while (ptr < end_ptr)` loops to be skipped correctly.
  // In this case, `ptr` will remain `line->text`.

  // Handle field separation based on the global 'tab' character.
  if (tab != TAB_DEFAULT)
    {
      // Custom separator: iterate `current_sword` times, skipping content then the separator.
      // This path is taken when a specific tab character is defined (`-t` option).
      // Fields are delimited by `tab`. We move `ptr` past `current_sword` such delimiters.
      while (current_sword > 0 && ptr < end_ptr)
        {
          // Skip characters that are not the separator (this is the field's content).
          while (ptr < end_ptr && *ptr != tab)
            ++ptr;

          // If a separator was found (or we hit `end_ptr`), advance `ptr` past it
          // to position it at the beginning of the *next* potential field.
          if (ptr < end_ptr)
            ++ptr; // Skip the custom tab character.

          current_sword--;
        }
    }
  else
    {
      // Default separator: whitespace.
      // This path is taken when no specific tab character is defined.
      // Fields are delimited by sequences of blank characters.
      // The original comment "The leading field separator itself is included in a field when -t is absent"
      // implies that the field is considered to start *after* the blanks that precede it.
      while (current_sword > 0 && ptr < end_ptr)
        {
          // Skip leading blank characters (these are part of the separator).
          while (ptr < end_ptr && blanks[to_uchar (*ptr)])
            ++ptr;

          // Skip non-blank characters (this is the field's actual content).
          while (ptr < end_ptr && !blanks[to_uchar (*ptr)])
            ++ptr;

          current_sword--;
        }
    }

  // If `key->skipsblanks` is true, skip any leading blanks at the current `ptr` position.
  // This applies *after* the field skipping, to determine the exact start within the field.
  if (key->skipsblanks)
    while (ptr < end_ptr && blanks[to_uchar (*ptr)])
      ++ptr;

  // Advance `ptr` by `schar_offset` characters.
  // The original logic clamped `ptr` to `line->text + line->length - 1` (the last character).
  // If `line->length` is 0, it clamped `ptr` to `line->text`.
  // We determine the maximum allowed return pointer based on the line's length.
  char *max_return_ptr = (line->length > 0) ? (end_ptr - 1) : line->text;

  ptr += schar_offset;
  
  // Clamp `ptr` to `max_return_ptr` if it has advanced beyond it.
  // This preserves the original behavior of not returning a pointer past the last character
  // of the line's content. For an empty line, it correctly returns `line->text`.
  if (ptr > max_return_ptr)
    ptr = max_return_ptr;

  return ptr;
}

/* Return the limit of (a pointer to the first character after) the field
   in LINE specified by KEY. */

#include <stddef.h> // For size_t
#include <string.h> // For memchr
#include <stdbool.h> // For bool

// Helper to safely convert char to unsigned char for array indexing
// This is a common pattern to ensure correct behavior with `char` types
// that might be signed by default on some platforms, when used as array indices.
#ifndef to_uchar
#define to_uchar(c) ((unsigned char) (c))
#endif

// Forward declarations for helper functions
// These assume `tab`, `TAB_DEFAULT`, `blanks` are globally accessible.
static char *skip_tab_field(char *p, char *end, char delimiter, bool advance_past_delim_if_possible);
static char *skip_blank_field(char *p, char *end, const bool *blanks_map);
static char *find_field_end(char *p, char *end, char delimiter, const bool *blanks_map);


ATTRIBUTE_PURE
static char *
limfield (struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text;
  char *lim = ptr + line->length; // 'lim' is a one-past-the-end pointer for the line buffer.

  size_t eword = key->eword;
  size_t echar = key->echar;

  // If echar is 0, it indicates that the entire field (up to the next delimiter or end of line)
  // should be skipped. To achieve this with field counting, we increment eword.
  if (echar == 0)
    {
      eword++;
    }

  // Phase 1: Advance 'ptr' past 'eword' fields.
  // The exact method of skipping fields depends on whether a custom 'tab' delimiter is used.
  if (tab != TAB_DEFAULT)
    {
      while (ptr < lim && eword--)
        {
          // The `(eword || echar)` condition is crucial.
          // For the last field being counted (`eword` becomes 0), if `echar` is also 0,
          // we do NOT advance 'ptr' past the delimiter, leaving it pointing at the delimiter.
          // Otherwise, 'ptr' is advanced past the delimiter.
          ptr = skip_tab_field(ptr, lim, tab, (eword || echar));
        }
    }
  else // Blank-separated fields
    {
      while (ptr < lim && eword--)
        {
          // For blank-separated fields, `skip_blank_field` inherently advances 'ptr'
          // past the field's content and trailing blanks to the start of the next logical field.
          ptr = skip_blank_field(ptr, lim, blanks);
        }
    }

#ifdef POSIX_UNSPECIFIED
  // Phase 2: If `POSIX_UNSPECIFIED` behavior is enabled, adjust 'lim'
  // to point to the exclusive end of the *current* field that 'ptr' is pointing into.
  // This 'lim' then acts as the upper bound for subsequent character-based skipping.
  lim = find_field_end(ptr, lim, tab, blanks);
#endif

  // Phase 3: If `echar` is non-zero, advance 'ptr' by 'echar' positions
  // within the current field, respecting the adjusted 'lim'.
  if (echar != 0)
    {
      // If `skipeblanks` is enabled for the end field, skip any leading blanks
      // before applying the 'echar' offset.
      if (key->skipeblanks)
        {
          while (ptr < lim && blanks[to_uchar(*ptr)])
            {
              ++ptr;
            }
        }

      // Advance 'ptr' by 'echar' positions, but do not go beyond 'lim'.
      size_t available_bytes_in_field = lim - ptr;
      if (echar < available_bytes_in_field)
        {
          ptr += echar;
        }
      else
        {
          ptr = lim; // If 'echar' is too large, move 'ptr' to the field's end.
        }
    }

  return ptr;
}


// Helper function definitions:

// Advances 'p' past a single field in a tab-separated line.
// If `advance_past_delim_if_possible` is true and a delimiter is found,
// 'p' is moved to the character immediately following the delimiter.
// Otherwise, 'p' stops at the delimiter (or `end` if no delimiter is found).
static char *
skip_tab_field (char *p, char *end, char delimiter, bool advance_past_delim_if_possible)
{
  while (p < end && *p != delimiter)
    {
      ++p;
    }
  if (advance_past_delim_if_possible && p < end)
    {
      ++p; // Move past the delimiter
    }
  return p;
}

// Advances 'p' past a single field in a blank-separated line.
// 'p' is moved past any leading blanks, then past the field's content,
// ending at the first blank character after the field, or at `end`.
static char *
skip_blank_field (char *p, char *end, const bool *blanks_map)
{
  while (p < end && blanks_map[to_uchar(*p)])
    {
      ++p; // Skip leading blanks
    }
  while (p < end && !blanks_map[to_uchar(*p)])
    {
      ++p; // Skip field content
    }
  return p; // 'p' is now at the first blank after the field, or at 'end'
}

// Finds the exclusive end of the current field starting at 'p'.
// For tab-separated lines, it finds the next occurrence of `delimiter`.
// For blank-separated lines, it finds the first blank character after the field content.
// Returns `end` if the field continues to the end of the line without a delimiter.
static char *
find_field_end (char *p, char *end, char delimiter, const bool *blanks_map)
{
  if (p >= end)
    {
      return end;
    }

  if (delimiter != TAB_DEFAULT)
    {
      // Use memchr for efficient search for the next delimiter
      char *field_end_candidate = memchr (p, delimiter, end - p);
      return field_end_candidate ? field_end_candidate : end;
    }
  else
    {
      char *current_p = p;
      // Skip any leading blanks within the field range from 'p'
      while (current_p < end && blanks_map[to_uchar(*current_p)])
        {
          ++current_p;
        }
      // Find the end of the field's content (the first blank or 'end')
      while (current_p < end && !blanks_map[to_uchar(*current_p)])
        {
          ++current_p;
        }
      return current_p;
    }
}

/* Fill BUF reading from FP, moving buf->left bytes from the end
   of buf->buf to the beginning first.  If EOF is reached and the
   file wasn't terminated by a newline, supply one.  Set up BUF's line
   table too.  FILE is the name of the file corresponding to FP.
   Return true if some input was read.  */

static bool
fillbuf (struct buffer *buf, FILE *fp, char const *file)
{
  if (buf->eof)
    return false;

  if (buf->used != buf->left)
    {
      memmove (buf->buf, buf->buf + buf->used - buf->left, buf->left);
      buf->used = buf->left;
      buf->nlines = 0;
    }

  struct keyfield const *key_cfg = keylist;
  char eol_char = eolchar;
  size_t line_record_size = buf->line_bytes;
  size_t current_mergesize = merge_buffer_size - MIN_MERGE_BUFFER_SIZE;
  char *current_read_ptr = buf->buf + buf->used;

  while (true)
    {
      struct line *line_limit = buffer_linelim (buf);
      struct line *current_line_record = line_limit - buf->nlines;
      size_t available_buffer_bytes = (char *) line_limit - buf->nlines * line_record_size - current_read_ptr;
      char *line_start_ptr = buf->nlines ? current_line_record->text + current_line_record->length : buf->buf;

      if (line_record_size + 1 >= available_buffer_bytes)
        {
          // Not enough room for even a minimal line record + a byte.
          // This should trigger buffer resizing or indicates an edge case.
        }
      else
        {
          size_t bytes_to_read = (available_buffer_bytes - 1) / (line_record_size + 1);
          size_t bytes_actually_read = fread (current_read_ptr, 1, bytes_to_read, fp);
          char *read_limit_ptr = current_read_ptr + bytes_actually_read;
          available_buffer_bytes -= bytes_actually_read;

          if (bytes_actually_read != bytes_to_read)
            {
              if (ferror (fp))
                sort_die (_("read failed"), file);
              if (feof (fp))
                {
                  buf->eof = true;
                  if (current_read_ptr == read_limit_ptr)
                    return false;
                  if (line_start_ptr != read_limit_ptr && read_limit_ptr[-1] != eol_char)
                    *read_limit_ptr++ = eol_char;
                }
            }

          char *process_ptr = current_read_ptr;
          while (process_ptr < read_limit_ptr)
            {
              char *newline_ptr = memchr (process_ptr, eol_char, read_limit_ptr - process_ptr);
              if (!newline_ptr)
                break; // No more full lines in the just-read chunk

              *newline_ptr = '\0'; // NUL-terminate the line
              process_ptr = newline_ptr + 1;
              current_line_record--;
              current_line_record->text = line_start_ptr;
              current_line_record->length = process_ptr - line_start_ptr;
              current_mergesize = MAX (current_mergesize, current_line_record->length);
              available_buffer_bytes -= line_record_size;

              if (key_cfg)
                {
                  current_line_record->keylim = (key_cfg->eword == SIZE_MAX
                                                 ? newline_ptr
                                                 : limfield (current_line_record, key_cfg));

                  if (key_cfg->sword != SIZE_MAX)
                    current_line_record->keybeg = begfield (current_line_record, key_cfg);
                  else
                    {
                      char *temp_key_beg = line_start_ptr;
                      if (key_cfg->skipsblanks)
                        while (blanks[to_uchar (*temp_key_beg)])
                          temp_key_beg++;
                      current_line_record->keybeg = temp_key_beg;
                    }
                }
              line_start_ptr = process_ptr;
            }
          current_read_ptr = read_limit_ptr;
        }

      if (buf->eof)
        break;

      buf->used = current_read_ptr - buf->buf;
      buf->nlines = line_limit - current_line_record;

      if (buf->nlines != 0)
        {
          buf->left = current_read_ptr - line_start_ptr;
          merge_buffer_size = current_mergesize + MIN_MERGE_BUFFER_SIZE;
          return true;
        }

      // No full lines processed, buffer needs to be expanded.
      idx_t line_alloc_capacity = buf->alloc / sizeof (struct line);
      buf->buf = xpalloc (buf->buf, &line_alloc_capacity, 1, -1, sizeof (struct line));
      buf->alloc = line_alloc_capacity * sizeof (struct line);

      // Recalculate current_read_ptr relative to the new buffer base
      current_read_ptr = buf->buf + buf->used;
    }
  return false;
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
  char const *read_p = *number;
  char ch;
  char max_digit = '\0';
  char const *current_end_p = *number; // Marks the current end of the successfully parsed number fragment

  // Phase 1: Scan integer part, handling thousands separators
  while (true)
    {
      if (c_isdigit (*read_p))
        {
          ch = *read_p++;
          if (max_digit < ch)
            max_digit = ch;
          current_end_p = read_p; // Update current_end_p to point *after* this digit
        }
      else if (*read_p == thousands_sep)
        {
          // A thousands separator must be followed by a digit.
          // If not, this separator (and anything after it) is not part of the number.
          if (!c_isdigit (*(read_p + 1)))
            {
              // The number ends at `current_end_p` (after the last valid digit before the invalid separator).
              break; 
            }
          read_p++; // Skip the thousands separator
          // Do NOT update current_end_p here. It only tracks valid digits.
        }
      else
        {
          // Not a digit, not a thousands_sep. Integer part ends here.
          break;
        }
    }

  // At this point:
  // - `current_end_p` points to the character *after* the last valid integer digit.
  //   If no digits were found, it's still at the initial `*number`.
  // - `read_p` points to the character that stopped the integer scan (or past the invalid thousands_sep).

  // Reset `read_p` to the end of the valid integer part for checking the decimal section.
  read_p = current_end_p; 

  // Phase 2: Check for decimal part
  if (*read_p == decimal_point)
    {
      read_p++; // Skip decimal point
      
      // Scan decimal digits
      while (c_isdigit (ch = *read_p))
        {
          if (max_digit < ch)
            max_digit = ch;
          read_p++;
        }
    }

  // `read_p` now points to the first character *not* part of the number.
  *number = read_p; 
  return max_digit;
}

/* Return an integer that represents the order of magnitude of the
   unit following the number.  The number may contain thousands
   separators and a decimal point, but it may not contain leading blanks.
   Negative numbers get negative orders; zero numbers have a zero order.  */

#ifndef UNIT_ORDER_ARRAY_SIZE
#define UNIT_ORDER_ARRAY_SIZE 256
#endif

ATTRIBUTE_PURE
static int
find_unit_order (char const *number)
{
  if (number == NULL) {
    return 0;
  }

  bool minus_sign = (*number == '-');
  char const *p = number + minus_sign;

  char max_digit = traverse_raw_number(&p);

  if (max_digit <= '0') {
    return 0;
  }

  unsigned char unit_char = (unsigned char)*p;

  if (unit_char == '\0' || unit_char >= UNIT_ORDER_ARRAY_SIZE) {
    return 0;
  }

  int order = unit_order[unit_char];

  return (minus_sign ? -order : order);
}

/* Compare numbers A and B ending in units with SI or IEC prefixes
       <none/unknown> < K/k < M < G < T < P < E < Z < Y < R < Q */

ATTRIBUTE_PURE
static int
human_numcompare (char const *a, char const *b)
{
  while (*a != '\0' && blanks[to_uchar (*a)])
    a++;
  while (*b != '\0' && blanks[to_uchar (*b)])
    b++;

  int diff = find_unit_order (a) - find_unit_order (b);
  return (diff ? diff : strnumcmp (a, b, decimal_point, thousands_sep));
}

/* Compare strings A and B as numbers without explicitly converting them to
   machine numbers.  Comparatively slow for short strings, but asymptotically
   hideously fast. */

ATTRIBUTE_PURE
static int
numcompare (char const *a, char const *b)
{
  while (*a != '\0' && blanks[to_uchar (*a)])
    a++;
  while (*b != '\0' && blanks[to_uchar (*b)])
    b++;

  return strnumcmp (a, b, decimal_point, thousands_sep);
}

#include <stdio.h>
#include <string.h>
#include <float.h> // For LDBL_MAX_10_EXP, LDBL_DECIMAL_DIG

// Define a sufficiently large buffer size to prevent truncation for long double
// string representations using %Lf. This calculation considers:
// 1 (sign) + LDBL_MAX_10_EXP (digits before decimal) + 1 (decimal point) +
// LDBL_DECIMAL_DIG (digits after decimal) + 1 (exponent char 'e') +
// 1 (exponent sign) + 5 (maximum exponent digits for LDBL_MAX_10_EXP) +
// 1 (null terminator) + a safety margin (e.g., 32 for NaN payloads).
// For common long double implementations (e.g., 80-bit or 128-bit extended precision),
// LDBL_MAX_10_EXP is around 4932 and LDBL_DECIMAL_DIG is around 21-36.
// This results in a length of approximately 5000 characters.
// Using a round number like 5120 ensures robustness.
#define LDBL_STRING_BUFFER_SIZE 5120

static int
nan_compare (long double a, long double b)
{
  char buf[2][LDBL_STRING_BUFFER_SIZE];

  // Use snprintf to safely convert long double values to their string representations.
  // The LDBL_STRING_BUFFER_SIZE is calculated to be large enough to prevent truncation
  // for all standard long double values, including NaN and Inf, thereby improving
  // reliability and ensuring accurate comparisons based on string content.
  snprintf(buf[0], LDBL_STRING_BUFFER_SIZE, "%Lf", a);
  snprintf(buf[1], LDBL_STRING_BUFFER_SIZE, "%Lf", b);

  // Compare the string representations.
  return strcmp(buf[0], buf[1]);
}

static int
general_numcompare (char const *sa, char const *sb)
{
  char *ea;
  char *eb;
  long double a = strtold (sa, &ea);
  long double b = strtold (sb, &eb);

  int a_is_conversion_error = (sa == ea);
  int b_is_conversion_error = (sb == eb);

  if (a_is_conversion_error && b_is_conversion_error)
    {
      return 0;
    }
  if (a_is_conversion_error)
    {
      return -1;
    }
  if (b_is_conversion_error)
    {
      return 1;
    }

  int a_is_nan = (a != a);
  int b_is_nan = (b != b);

  if (a_is_nan && b_is_nan)
    {
      return nan_compare (a, b);
    }
  if (a_is_nan)
    {
      return -1;
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
getmonth (char const *month_str, char **end_ptr)
{
  if (month_str == NULL)
    {
      return 0;
    }

  while (blanks[to_uchar (*month_str)])
    {
      month_str++;
    }

  size_t low_idx = 0;
  size_t high_idx = MONTHS_PER_YEAR;

  while (low_idx < high_idx)
    {
      size_t mid_idx = low_idx + (high_idx - low_idx) / 2;
      
      char const *current_input_ptr = month_str;
      char const *lookup_name_ptr = monthtab[mid_idx].name;
      int comparison_result = 0;

      while (*lookup_name_ptr != '\0')
        {
          unsigned char input_char_folded = fold_toupper[to_uchar(*current_input_ptr)];
          unsigned char lookup_char_val = to_uchar(*lookup_name_ptr);

          if (input_char_folded < lookup_char_val)
            {
              comparison_result = -1;
              break;
            }
          else if (input_char_folded > lookup_char_val)
            {
              comparison_result = 1;
              break;
            }
          
          current_input_ptr++;
          lookup_name_ptr++;
        }

      if (comparison_result == 0)
        {
          if (end_ptr)
            {
              *end_ptr = (char *) current_input_ptr;
            }
          return monthtab[mid_idx].val;
        }
      else if (comparison_result < 0)
        {
          high_idx = mid_idx;
        }
      else
        {
          low_idx = mid_idx + 1;
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
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

typedef int (*MD5_Init_func)(void *);
typedef int (*MD5_Update_func)(void *, const void *, size_t);
typedef int (*MD5_Final_func)(unsigned char *, void *);

static MD5_Init_func ptr_MD5_Init = NULL;
static MD5_Update_func ptr_MD5_Update = NULL;
static MD5_Final_func ptr_MD5_Final = NULL;

static void
link_libcrypto (void)
{
#if defined(DLOPEN_LIBCRYPTO) && defined(HAVE_OPENSSL_MD5)
  void *handle = dlopen (LIBCRYPTO_SONAME, RTLD_LAZY | RTLD_GLOBAL);
  if (!handle) {
    fprintf(stderr, "Error: Failed to open library '%s': %s\n", LIBCRYPTO_SONAME, dlerror());
    exit(EXIT_FAILURE);
  }

  ptr_MD5_Init = (MD5_Init_func)dlsym (handle, "MD5_Init");
  if (!ptr_MD5_Init) {
    fprintf(stderr, "Error: Failed to load symbol 'MD5_Init': %s\n", dlerror());
    dlclose(handle);
    exit(EXIT_FAILURE);
  }

  ptr_MD5_Update = (MD5_Update_func)dlsym (handle, "MD5_Update");
  if (!ptr_MD5_Update) {
    fprintf(stderr, "Error: Failed to load symbol 'MD5_Update': %s\n", dlerror());
    dlclose(handle);
    exit(EXIT_FAILURE);
  }

  ptr_MD5_Final = (MD5_Final_func)dlsym (handle, "MD5_Final");
  if (!ptr_MD5_Final) {
    fprintf(stderr, "Error: Failed to load symbol 'MD5_Final': %s\n", dlerror());
    dlclose(handle);
    exit(EXIT_FAILURE);
  }
#else
  ptr_MD5_Init = NULL;
  ptr_MD5_Update = NULL;
  ptr_MD5_Final = NULL;
#endif
}

/* A randomly chosen MD5 state, used for random comparison.  */
static struct md5_ctx random_md5_state;

/* Initialize the randomly chosen MD5 state.  */

static void
random_md5_state_init (char const *random_source)
{
  unsigned char buf[MD5_DIGEST_SIZE];
  struct randread_source *r;
  size_t bytes_read;
  char const *source_name = random_source ? random_source : "getrandom";

  r = randread_new (random_source, sizeof buf);
  if (!r)
    {
      sort_die (_("open failed"), source_name);
    }

  bytes_read = randread (r, buf, sizeof buf);
  if (bytes_read != sizeof buf)
    {
      sort_die (_("read failed: could not obtain full random data from %s"), source_name);
    }

  if (randread_free (r) != 0)
    {
      sort_die (_("close failed"), source_name);
    }

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

  if (errno != 0)
    {
      error (0, errno, _("string transformation failed"));
      error (0, 0, _("set LC_ALL='C' to work around the problem"));
      error (SORT_FAILURE, 0,
             _("the original string was %s"),
             quotearg_n_style (0, locale_quoting_style, src));
    }

  return translated_size;
}

/* Compare the keys TEXTA (of length LENA) and TEXTB (of length LENB)
   using one or more random hash functions.  TEXTA[LENA] and
   TEXTB[LENB] must be zero.  */

static void *xmalloc (size_t);
static void *xrealloc (void *, size_t);

#ifndef MIN
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#endif
#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

/* Assuming MD5_DIGEST_SIZE, md5_ctx, random_md5_state, md5_process_bytes, md5_finish_ctx are defined elsewhere. */
/* Assuming hard_LC_COLLATE is a global or external variable. */

typedef unsigned int uint32_t;
enum { MD5_DIGEST_SIZE = 16 };
struct md5_ctx { /* ... MD5 context members ... */ };
extern struct md5_ctx random_md5_state;
extern void md5_process_bytes(const void *, size_t, struct md5_ctx *);
extern void md5_finish_ctx(struct md5_ctx *, uint32_t *);

extern bool hard_LC_COLLATE;

/* Helper struct for managing dynamic buffer */
typedef struct {
    char *ptr;           /* Current pointer to the buffer (could be stackbuf or allocated_ptr) */
    size_t size;         /* Current capacity of the buffer */
    void *allocated_ptr; /* Pointer to heap-allocated memory (or NULL if using stackbuf) */
} dynamic_buffer_t;

/* Initialize dynamic buffer with a stack-allocated buffer */
static void init_dynamic_buffer(dynamic_buffer_t *db, char *stack_buf, size_t stack_buf_size) {
    db->ptr = stack_buf;
    db->size = stack_buf_size;
    db->allocated_ptr = NULL;
}

/* Ensure buffer has at least 'required_size' capacity, growing if necessary.
   Uses xmalloc/xrealloc which are assumed to not return NULL. */
static void ensure_buffer_capacity(dynamic_buffer_t *db, size_t required_size) {
    if (db->size < required_size) {
        size_t new_size = required_size;
        /* Grow by factor (e.g., 1.5x) but ensure it's at least 'required_size'. */
        /* Check for overflow before multiplying. */
        if (new_size < SIZE_MAX / 3 * 2) {
             new_size = MAX(new_size, db->size * 3 / 2);
        }
        
        char *new_ptr;
        if (db->allocated_ptr == NULL) { /* First heap allocation */
            new_ptr = xmalloc(new_size);
        } else { /* Reallocate existing heap buffer */
            new_ptr = xrealloc(db->allocated_ptr, new_size);
        }
        db->ptr = new_ptr;
        db->allocated_ptr = new_ptr;
        db->size = new_size;
    }
}

/* Free dynamically allocated memory if any */
static void free_dynamic_buffer(dynamic_buffer_t *db) {
    free(db->allocated_ptr); /* free(NULL) is safe */
    db->allocated_ptr = NULL; /* Prevent double-free */
    db->ptr = NULL;
    db->size = 0;
}

static int
compare_random (char *restrict texta, size_t lena,
                char *restrict textb, size_t lenb)
{
  /* XFRM_DIFF records the equivalent of memcmp on the transformed
     data.  This is used to break ties if there is a checksum
     collision, and this is good enough given the astronomically low
     probability of a collision.  */
  int xfrm_diff = 0;

  char stackbuf[4000];
  dynamic_buffer_t db;
  init_dynamic_buffer(&db, stackbuf, sizeof stackbuf);
  
  uint32_t dig[2][MD5_DIGEST_SIZE / sizeof (uint32_t)];
  struct md5_ctx s[2];
  s[0] = s[1] = random_md5_state;

  /* Store original pointers and lengths for potential tie-breaker memcmp at the end. */
  char *const original_texta = texta;
  size_t const original_lena = lena;
  char *const original_textb = textb;
  size_t const original_lenb = lenb;

  if (hard_LC_COLLATE)
    {
      char const *current_texta_segment_start = texta;
      char const *current_textb_segment_start = textb;
      char const *end_texta = texta + lena;
      char const *end_textb = textb + lenb;

      while (current_texta_segment_start < end_texta || current_textb_segment_start < end_textb)
        {
          size_t transformed_len_a_segment = 0;
          size_t transformed_len_b_segment = 0;

          /* Determine required sizes for the transformed segments.
             strxfrm(NULL, src, 0) returns length *without* null terminator. Add 1 for the null. */
          if (current_texta_segment_start < end_texta) {
            transformed_len_a_segment = strxfrm(NULL, current_texta_segment_start, 0) + 1;
          }
          if (current_textb_segment_start < end_textb) {
            transformed_len_b_segment = strxfrm(NULL, current_textb_segment_start, 0) + 1;
          }

          size_t total_needed_buffer_size = transformed_len_a_segment + transformed_len_b_segment;
          
          /* If both segments are exhausted, break. This check is primarily for robustness
             though the while condition should handle it. */
          if (total_needed_buffer_size == 0) {
              break;
          }

          ensure_buffer_capacity(&db, total_needed_buffer_size);

          /* Perform transformation into the buffer.
             strxfrm guarantees null-termination if n > 0 and the transformed string fits.
             Since transformed_len_a_segment includes the null and is derived from strxfrm(NULL, ...),
             it is guaranteed to fit. */
          if (current_texta_segment_start < end_texta) {
            strxfrm(db.ptr, current_texta_segment_start, transformed_len_a_segment);
          }
          
          if (current_textb_segment_start < end_textb) {
            strxfrm(db.ptr + transformed_len_a_segment, 
                    current_textb_segment_start, 
                    transformed_len_b_segment);
          }

          /* Advance input pointers past current null-terminated segment. */
          if (current_texta_segment_start < end_texta) {
            current_texta_segment_start += strlen(current_texta_segment_start) + 1;
          }
          if (current_textb_segment_start < end_textb) {
            current_textb_segment_start += strlen(current_textb_segment_start) + 1;
          }

          /* Accumulate the transformed data in the corresponding checksums. */
          if (transformed_len_a_segment > 0) {
            md5_process_bytes (db.ptr, transformed_len_a_segment, &s[0]);
          }
          if (transformed_len_b_segment > 0) {
            md5_process_bytes (db.ptr + transformed_len_a_segment, transformed_len_b_segment, &s[1]);
          }

          /* Update the tiebreaker comparison of the transformed data. */
          if (! xfrm_diff)
            {
              xfrm_diff = memcmp (db.ptr, db.ptr + transformed_len_a_segment, 
                                  MIN (transformed_len_a_segment, transformed_len_b_segment));
              if (! xfrm_diff)
                xfrm_diff = (transformed_len_a_segment < transformed_len_b_segment) ? -1 : ((transformed_len_a_segment > transformed_len_b_segment) ? 1 : 0);
            }
        }
    }

  /* Compute and compare the checksums. */
  /* If hard_LC_COLLATE is true, MD5s were accumulated in the loop.
     Otherwise, process the original bytes. */
  if (!hard_LC_COLLATE) {
    md5_process_bytes (original_texta, original_lena, &s[0]);
    md5_process_bytes (original_textb, original_lenb, &s[1]);
  }
  md5_finish_ctx (&s[0], dig[0]);
  md5_finish_ctx (&s[1], dig[1]);
  int diff = memcmp (dig[0], dig[1], sizeof dig[0]);

  /* Fall back on the tiebreaker if the checksums collide. */
  if (! diff)
    {
      if (! xfrm_diff) /* If transformed strings were equal, or no transformation was done. */
        {
          /* If xfrm_diff is still 0, it means either:
             1. hard_LC_COLLATE was true, and all transformed segments were identical.
             2. hard_LC_COLLATE was false, so xfrm_diff was never updated.
             In both cases, the final tie-breaker should be a direct binary comparison of the *original* full strings. */
          xfrm_diff = memcmp (original_texta, original_textb, MIN (original_lena, original_lenb));
          if (! xfrm_diff)
            xfrm_diff = (original_lena < original_lenb) ? -1 : ((original_lena > original_lenb) ? 1 : 0);
        }

      diff = xfrm_diff;
    }

  free_dynamic_buffer(&db);

  return diff;
}

/* Return the printable width of the block of memory starting at
   TEXT and ending just before LIM, counting each tab as one byte.
   FIXME: Should we generally be counting non printable chars?  */

static size_t
debug_width (char const *text, char const *lim)
{
  if (text == NULL || lim == NULL || lim < text)
    {
      return 0;
    }

  size_t len = (size_t)(lim - text);

  int initial_width_result = mbsnwidth (text, len, 0);

  if (initial_width_result < 0)
    {
      return 0;
    }

  size_t width = (size_t)initial_width_result;

  for (char const *current_char = text; current_char < lim; ++current_char)
    {
      if (*current_char == '\t')
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
  for (size_t i = 0; i < offset; ++i)
    putchar (' ');

  if (width == 0)
    printf (_("^ no match for key\n"));
  else
    {
      for (size_t i = 0; i < width; ++i)
        putchar ('_');

      putchar ('\n');
    }
}

/* Return true if KEY is a numeric key.  */

static inline bool
key_numeric (struct keyfield const *key)
{
  return key->numeric || key->general_numeric || key->human_numeric;
}

/* For LINE, output a debugging line that underlines KEY in LINE.
   If KEY is null, underline the whole line.  */

static void
debug_key (struct line const *line, struct keyfield const *key)
{
  char *line_text = line->text;
  char *line_text_limit = line_text + line->length; // Pointer one past the last character

  char *field_start_ptr = line_text;
  char *field_end_ptr = line_text_limit - 1; // Pointer to the last character of the line

  // Step 1: Determine the initial field boundaries based on key definition.
  // `begfield` and `limfield` are assumed to return valid pointers within line_text.
  if (key)
    {
      if (key->sword != SIZE_MAX)
        field_start_ptr = begfield (line, key);
      if (key->eword != SIZE_MAX)
        {
          field_end_ptr = limfield (line, key);
          // If the field ends before it starts, treat it as an empty field,
          // effectively starting and ending at field_start_ptr.
          field_end_ptr = MAX (field_start_ptr, field_end_ptr);
        }

      // Step 2: Further process and "tighten" the field_end_ptr based on key type.
      // This applies if 'skipsblanks' is set (for whole line keys), or if it's a month/numeric key.
      bool needs_value_parsing =
        (key->skipsblanks && key->sword == SIZE_MAX) || key->month || key_numeric (key);

      if (needs_value_parsing)
        {
          // Temporarily null-terminate the string at field_end_ptr for parsing functions.
          // We assume field_end_ptr is a valid, writable pointer within the line_text buffer.
          char saved_char_at_end = *field_end_ptr;
          *field_end_ptr = '\0';

          // Advance field_start_ptr past any leading blanks within the field's current bounds.
          while (field_start_ptr < field_end_ptr && blanks[to_uchar (*field_start_ptr)])
            field_start_ptr++;

          // `final_field_end_ptr` will store the tightened end of the field.
          // Initialize it to the current `field_end_ptr`. This handles cases where
          // `needs_value_parsing` is true (e.g., `skipsblanks`) but no specific
          // value-based parsing (month/numeric) is performed.
          char *final_field_end_ptr = field_end_ptr;

          // Only attempt value-based parsing if there's actual content within the field.
          if (field_start_ptr < field_end_ptr)
            {
              if (key->month)
                getmonth (field_start_ptr, &final_field_end_ptr);
              else if (key->general_numeric)
                ignore_value (strtold (field_start_ptr, &final_field_end_ptr));
              else if (key->numeric || key->human_numeric)
                {
                  char const *current_pos = field_start_ptr;
                  // Handle optional leading sign for numbers. Ensure it's not just a standalone '-'.
                  if (*current_pos == '-' && current_pos + 1 < field_end_ptr)
                    current_pos++;

                  // Parse the raw number part. `traverse_raw_number` advances `current_pos`.
                  char max_digit = traverse_raw_number (&current_pos);
                  if ('0' <= max_digit) // Check if at least one digit was found.
                    {
                      // For human-numeric, check for a unit character immediately after the number.
                      if (key->human_numeric && unit_order[(unsigned char)*current_pos])
                        final_field_end_ptr = (char *)current_pos + 1; // Include the unit character.
                      else
                        final_field_end_ptr = (char *)current_pos;     // End of the number itself.
                    }
                  else
                    final_field_end_ptr = field_start_ptr; // No valid number found, field is effectively empty.
                }
              // If `needs_value_parsing` is true but none of the above specific key types match,
              // `final_field_end_ptr` remains as initialized (field_end_ptr).
            }
          else
            {
              // If `field_start_ptr` is now at or beyond `field_end_ptr` after skipping blanks,
              // it means the field is empty or contains only blanks.
              // In this case, `final_field_end_ptr` should align with `field_start_ptr` for a zero-width field.
              final_field_end_ptr = field_start_ptr;
            }

          field_end_ptr = final_field_end_ptr;   // Update the effective field end pointer.
          *field_end_ptr = saved_char_at_end; // Restore the character that was temporarily replaced.
        }
    }

  // Step 3: Calculate offset and width, then mark the key.
  size_t offset = debug_width (line_text, field_start_ptr);
  size_t width = debug_width (field_start_ptr, field_end_ptr);
  mark_key (offset, width);
}

/* Debug LINE by underlining its keys.  */

static void
debug_line (struct line const *line)
{
  struct keyfield const *current_key = keylist;
  int const continue_after_list_empty = ! (unique || stable);

  debug_key(line, current_key);

  if (current_key != NULL) {
    while ((current_key = current_key->next) != NULL) {
      debug_key(line, current_key);
    }

    if (continue_after_list_empty) {
      debug_key(line, NULL);
    }
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
  /* if (key->reverse) */
  /*   return false; */

  return true;
}

/* Convert a key to the short options used to specify it.  */

static size_t
key_to_opts (struct keyfield const *key, char *opts, size_t opts_size)
{
  char *current = opts;
  size_t total_len = 0;
  size_t remaining_space = opts_size;

  if (key->skipsblanks || key->skipeblanks) {
    if (remaining_space > 1) {
      *current++ = 'b';
      remaining_space--;
    }
    total_len++;
  }

  if (key->ignore == nondictionary) {
    if (remaining_space > 1) {
      *current++ = 'd';
      remaining_space--;
    }
    total_len++;
  }

  if (key->translate) {
    if (remaining_space > 1) {
      *current++ = 'f';
      remaining_space--;
    }
    total_len++;
  }

  if (key->general_numeric) {
    if (remaining_space > 1) {
      *current++ = 'g';
      remaining_space--;
    }
    total_len++;
  }

  if (key->human_numeric) {
    if (remaining_space > 1) {
      *current++ = 'h';
      remaining_space--;
    }
    total_len++;
  }

  if (key->ignore == nonprinting) {
    if (remaining_space > 1) {
      *current++ = 'i';
      remaining_space--;
    }
    total_len++;
  }

  if (key->month) {
    if (remaining_space > 1) {
      *current++ = 'M';
      remaining_space--;
    }
    total_len++;
  }

  if (key->numeric) {
    if (remaining_space > 1) {
      *current++ = 'n';
      remaining_space--;
    }
    total_len++;
  }

  if (key->random) {
    if (remaining_space > 1) {
      *current++ = 'R';
      remaining_space--;
    }
    total_len++;
  }

  if (key->reverse) {
    if (remaining_space > 1) {
      *current++ = 'r';
      remaining_space--;
    }
    total_len++;
  }

  if (key->version) {
    if (remaining_space > 1) {
      *current++ = 'V';
      remaining_space--;
    }
    total_len++;
  }

  if (opts_size > 0)
    *current = '\0';

  return total_len;
}

/* Output data independent key warnings to stderr.  */

static void
warn_obsolescent_key_syntax(struct keyfield const *key, unsigned long keynum)
{
  size_t sword_val = key->sword;
  size_t eword_val = key->eword;

  if (sword_val == SIZE_MAX)
    sword_val = 0;

  char tmp[INT_BUFSIZE_BOUND (uintmax_t)];
  char obuf[2 * INT_BUFSIZE_BOUND (uintmax_t) + 4];
  char nbuf[2 * INT_BUFSIZE_BOUND (uintmax_t) + 5];

  int obuf_len = snprintf(obuf, sizeof(obuf), "+%s", umaxtostr(sword_val, tmp));
  if (obuf_len < 0 || (size_t)obuf_len >= sizeof(obuf))
    obuf_len = sizeof(obuf) - 1;

  if (eword_val != SIZE_MAX)
    {
      int res = snprintf(obuf + obuf_len, sizeof(obuf) - obuf_len, " -%s", umaxtostr(eword_val + 1, tmp));
      if (res < 0 || (size_t)res >= (sizeof(obuf) - obuf_len))
        obuf[sizeof(obuf) - 1] = '\0';
    }

  size_t nbuf_eword_component = (eword_val == SIZE_MAX ? 0 : eword_val) + 1 + (key->echar == SIZE_MAX);

  int nbuf_len = snprintf(nbuf, sizeof(nbuf), "-k %s", umaxtostr(sword_val + 1, tmp));
  if (nbuf_len < 0 || (size_t)nbuf_len >= sizeof(nbuf))
    nbuf_len = sizeof(nbuf) - 1;

  if (eword_val != SIZE_MAX)
    {
      int res = snprintf(nbuf + nbuf_len, sizeof(nbuf) - nbuf_len, ",%s", umaxtostr(nbuf_eword_component, tmp));
      if (res < 0 || (size_t)res >= (sizeof(nbuf) - nbuf_len))
        nbuf[sizeof(nbuf) - 1] = '\0';
    }

  error (0, 0, _("obsolescent key %s used; consider %s instead"),
         quote_n (0, obuf), quote_n (1, nbuf));
}

static void
warn_blanks_significant(struct keyfield const *key, unsigned long keynum,
                        bool zero_width, bool gkey_only)
{
  if (zero_width || gkey_only || tab != TAB_DEFAULT)
    return;

  bool implicit_skip_blanks = key_numeric(key) || key->month;
  bool line_offset_case = key->eword == 0 && key->echar != 0;

  if (line_offset_case)
    return;

  bool warn_about_leading_blanks =
      (!key->skipsblanks && (!implicit_skip_blanks || key->schar))
      || (!key->skipeblanks && key->echar);

  if (warn_about_leading_blanks)
    error(0, 0, _("leading blanks are significant in key %lu; "
                   "consider also specifying 'b'"), keynum);
}

static void
warn_numeric_field_spanning(struct keyfield const *key, unsigned long keynum,
                            bool gkey_only,
                            bool *basic_numeric_field_span_p,
                            bool *general_numeric_field_span_p)
{
  if (gkey_only || !key_numeric(key))
    return;

  size_t sword_adjusted = key->sword;
  if (sword_adjusted == SIZE_MAX)
    sword_adjusted = 0;
  size_t display_sword = sword_adjusted + 1;

  size_t eword_adjusted = key->eword;
  if (eword_adjusted == SIZE_MAX)
    eword_adjusted = 0;
  size_t display_eword = eword_adjusted + 1;

  bool spans_multiple_fields = (display_eword == 0 || display_sword < display_eword);

  if (spans_multiple_fields)
    {
      error(0, 0, _("key %lu is numeric and spans multiple fields"), keynum);
      if (key->general_numeric)
        *general_numeric_field_span_p = true;
      else
        *basic_numeric_field_span_p = true;
    }
}

static bool
warn_number_locale_separators(bool basic_numeric_field_span,
                              bool general_numeric_field_span)
{
  bool warned_this_block = false;

  bool thousands_sep_collides = (tab == TAB_DEFAULT
                                 ? (thousands_sep != NON_CHAR && isblank(to_uchar(thousands_sep)))
                                 : (tab == thousands_sep));
  if (basic_numeric_field_span && thousands_sep_collides)
    {
      error(0, 0,
            _("field separator %s is treated as a "
              "group separator in numbers"),
            quote(((char[]) {thousands_sep, 0})));
      warned_this_block = true;
    }

  bool decimal_point_collides = (tab == TAB_DEFAULT
                                 ? (thousands_sep != NON_CHAR && isblank(to_uchar(decimal_point)))
                                 : (tab == decimal_point));
  if (basic_numeric_field_span || general_numeric_field_span)
    {
      if (decimal_point_collides)
        {
          error(0, 0,
                _("field separator %s is treated as a "
                  "decimal point in numbers"),
                quote(((char[]) {decimal_point, 0})));
          warned_this_block = true;
        }
      else if (tab == '-')
        {
          error(0, 0,
                _("field separator %s is treated as a "
                  "minus sign in numbers"),
                quote(((char[]) {tab, 0})));
          warned_this_block = true;
        }
      else if (general_numeric_field_span && tab == '+')
        {
          error(0, 0,
                _("field separator %s is treated as a "
                  "plus sign in numbers"),
                quote(((char[]) {tab, 0})));
          warned_this_block = true;
        }
    }
  return warned_this_block;
}

static void
warn_ignored_global_options(struct keyfield ugkey, bool stable_sort,
                            bool unique_sort, bool keylist_exists)
{
  bool ugkey_has_remaining_options = !default_key_compare(&ugkey);
  bool ugkey_reverse_applies_to_last_resort = ugkey.reverse && (stable_sort || unique_sort) && keylist_exists;

  bool original_ugkey_reverse = ugkey.reverse;
  if (!(stable_sort || unique_sort))
    ugkey.reverse = false;

  char opts[sizeof short_options];
  key_to_opts(&ugkey, opts);

  if (ugkey_has_remaining_options || ugkey_reverse_applies_to_last_resort)
    {
      error(0, 0,
            ngettext ("option '-%s' is ignored",
                      "options '-%s' are ignored",
                      select_plural (strlen(opts))), opts);
    }

  ugkey.reverse = original_ugkey_reverse;

  if (ugkey.reverse && !(stable_sort || unique_sort) && keylist_exists)
    error(0, 0, _("option '-r' only applies to last-resort comparison"));
}

static void
key_warnings (struct keyfield const *gkey, bool gkey_only)
{
  struct keyfield ugkey = *gkey;
  unsigned long keynum = 1;

  bool basic_numeric_field = false;
  bool general_numeric_field = false;
  bool basic_numeric_field_span = false;
  bool general_numeric_field_span = false;

  for (struct keyfield const *key = keylist; key; key = key->next, keynum++)
    {
      if (key_numeric(key))
        {
          if (key->general_numeric)
            general_numeric_field = true;
          else
            basic_numeric_field = true;
        }

      if (key->traditional_used)
        warn_obsolescent_key_syntax(key, keynum);

      bool zero_width = key->sword != SIZE_MAX && key->eword < key->sword;
      if (zero_width)
        error(0, 0, _("key %lu has zero width and will be ignored"), keynum);

      warn_blanks_significant(key, keynum, zero_width, gkey_only);

      warn_numeric_field_spanning(key, keynum, gkey_only,
                                  &basic_numeric_field_span, &general_numeric_field_span);

      if (ugkey.ignore && (ugkey.ignore == key->ignore))
        ugkey.ignore = nullptr;
      if (ugkey.translate && (ugkey.translate == key->translate))
        ugkey.translate = nullptr;
      ugkey.skipsblanks &= !key->skipsblanks;
      ugkey.skipeblanks &= !key->skipeblanks;
      ugkey.month &= !key->month;
      ugkey.numeric &= !key->numeric;
      ugkey.general_numeric &= !key->general_numeric;
      ugkey.human_numeric &= !key->human_numeric;
      ugkey.random &= !key->random;
      ugkey.version &= !key->version;
      ugkey.reverse &= !key->reverse;
    }

  bool number_locale_warned = warn_number_locale_separators(basic_numeric_field_span, general_numeric_field_span);

  if ((basic_numeric_field || general_numeric_field) && !number_locale_warned)
    {
      error(0, 0,
            _("numbers use %s as a decimal point in this locale"),
            quote(((char[]) {decimal_point, 0})));
    }

  if (basic_numeric_field && thousands_sep_ignored)
    {
      error(0, 0,
            _("the multi-byte number group separator "
              "in this locale is not supported"));
    }

  warn_ignored_global_options(ugkey, stable, unique, keylist != nullptr);
}

/* Return either the sense of DIFF or its reverse, depending on REVERSED.
   If REVERSED, do not simply negate DIFF as that can mishandle INT_MIN.  */

static int
diff_reversed (int diff, bool reversed)
{
  if (reversed)
    {
      return (diff < 0) - (diff > 0);
    }
  else
    {
      return diff;
    }
}

/* Compare two lines A and B trying every key in sequence until there
   are no more keys or a difference is found. */

static char*
buffer_and_process_key_segment(char const *text, size_t len,
                               char const *translate, bool const *ignore,
                               char *stack_buffer_ptr, size_t stack_buffer_size,
                               void **allocated_ptr, size_t *processed_len_out)
{
    *allocated_ptr = nullptr;
    *processed_len_out = 0;

    size_t max_buf_len = len + 1;

    char *buf;
    if (max_buf_len > stack_buffer_size) {
        buf = xmalloc(max_buf_len);
        *allocated_ptr = buf;
    } else {
        buf = stack_buffer_ptr;
    }

    size_t current_len = 0;
    for (size_t i = 0; i < len; ++i) {
        unsigned char c = to_uchar(text[i]);
        if (! (ignore && ignore[c])) {
            buf[current_len++] = (translate ? translate[c] : text[i]);
        }
    }
    buf[current_len] = '\0';
    *processed_len_out = current_len;
    return buf;
}

static int
compare_with_ignore_and_translate(char const *texta, char const *lima,
                                  char const *textb, char const *limb,
                                  char const *translate, bool const *ignore)
{
    while (true) {
        while (texta < lima && ignore[to_uchar(*texta)]) {
            ++texta;
        }
        while (textb < limb && ignore[to_uchar(*textb)]) {
            ++textb;
        }

        bool a_has_more = (texta < lima);
        bool b_has_more = (textb < limb);

        if (!a_has_more || !b_has_more) {
            return a_has_more - b_has_more;
        }

        unsigned char char_a = to_uchar(*texta);
        unsigned char char_b = to_uchar(*textb);

        int diff = (translate ? to_uchar(translate[char_a]) : char_a) -
                   (translate ? to_uchar(translate[char_b]) : char_b);

        if (diff) {
            return diff;
        }

        ++texta;
        ++textb;
    }
}

static void
get_key_field_pointers(struct line const *line, struct keyfield const *key,
                       char **text_out, char **lim_out)
{
    if (key->eword != SIZE_MAX) {
        *lim_out = limfield(line, key);
    } else {
        *lim_out = line->text + line->length - 1;
    }

    if (key->sword != SIZE_MAX) {
        *text_out = begfield(line, key);
    } else {
        *text_out = line->text;
        if (key->skipsblanks) {
            char *current_text = *text_out;
            while (current_text < *lim_out && blanks[to_uchar(*current_text)]) {
                ++current_text;
            }
            *text_out = current_text;
        }
    }
}

static int
keycompare (struct line const *a, struct line const *b)
{
  struct keyfield *key = keylist;
  int diff;

  char *texta_ptr = a->keybeg;
  char *textb_ptr = b->keybeg;
  char *lima_ptr = a->keylim;
  char *limb_ptr = b->keylim;

  while (true)
    {
      lima_ptr = MAX (texta_ptr, lima_ptr);
      limb_ptr = MAX (textb_ptr, limb_ptr);

      size_t lena = lima_ptr - texta_ptr;
      size_t lenb = limb_ptr - textb_ptr;

      char const *translate = key->translate;
      bool const *ignore = key->ignore;

      if (hard_LC_COLLATE || key_numeric(key) || key->month || key->random || key->version)
        {
          char stack_buffer[4000];
          void *allocated_a = nullptr;
          void *allocated_b = nullptr;
          size_t processed_len_a, processed_len_b;

          char *processed_text_a = buffer_and_process_key_segment(texta_ptr, lena,
                                                                  translate, ignore,
                                                                  stack_buffer, sizeof(stack_buffer),
                                                                  &allocated_a, &processed_len_a);

          char *stack_buffer_b_start = stack_buffer;
          size_t stack_buffer_b_size = sizeof(stack_buffer);
          if (processed_text_a == stack_buffer) {
              size_t offset = processed_len_a + 1;
              if (offset < sizeof(stack_buffer)) {
                  stack_buffer_b_start = stack_buffer + offset;
                  stack_buffer_b_size = sizeof(stack_buffer) - offset;
              } else {
                  stack_buffer_b_size = 0;
              }
          }

          char *processed_text_b = buffer_and_process_key_segment(textb_ptr, lenb,
                                                                  translate, ignore,
                                                                  stack_buffer_b_start, stack_buffer_b_size,
                                                                  &allocated_b, &processed_len_b);

          if (key->numeric)
            diff = numcompare (processed_text_a, processed_text_b);
          else if (key->general_numeric)
            diff = general_numcompare (processed_text_a, processed_text_b);
          else if (key->human_numeric)
            diff = human_numcompare (processed_text_a, processed_text_b);
          else if (key->month)
            diff = getmonth (processed_text_a, nullptr) - getmonth (processed_text_b, nullptr);
          else if (key->random)
            diff = compare_random (processed_text_a, processed_len_a, processed_text_b, processed_len_b);
          else if (key->version)
            diff = filenvercmp (processed_text_a, processed_len_a, processed_text_b, processed_len_b);
          else
            {
              if (processed_len_a == 0)
                diff = - NONZERO (processed_len_b);
              else if (processed_len_b == 0)
                diff = 1;
              else
                diff = xmemcoll0 (processed_text_a, processed_len_a + 1, processed_text_b, processed_len_b + 1);
            }

          free (allocated_a);
          free (allocated_b);
        }
      else if (ignore)
        {
          diff = compare_with_ignore_and_translate(texta_ptr, lima_ptr,
                                                   textb_ptr, limb_ptr,
                                                   translate, ignore);
        }
      else
        {
          size_t lenmin = MIN (lena, lenb);
          if (lenmin == 0)
            diff = 0;
          else if (translate)
            {
              size_t i = 0;
              do
                {
                  diff = (to_uchar (translate[to_uchar (texta_ptr[i])])
                          - to_uchar (translate[to_uchar (textb_ptr[i])]));
                  if (diff)
                    break;
                  i++;
                }
              while (i < lenmin);
            }
          else
            diff = memcmp (texta_ptr, textb_ptr, lenmin);

          if (! diff)
            diff = _GL_CMP (lena, lenb);
        }

      if (diff)
        break;

      key = key->next;
      if (! key)
        return 0;

      get_key_field_pointers(a, key, &texta_ptr, &lima_ptr);
      get_key_field_pointers(b, key, &textb_ptr, &limb_ptr);
    }

  return diff_reversed (diff, key->reverse);
}

/* Compare two lines A and B, returning negative, zero, or positive
   depending on whether A compares less than, equal to, or greater than B. */

static int
compare (struct line const *a, struct line const *b)
{
  int diff;
  size_t alen, blen;

  if (keylist)
    {
      diff = keycompare (a, b);
      if (diff || unique || stable)
        return diff;
    }

  alen = a->length - 1;
  blen = b->length - 1;

  if (alen == 0)
    {
      if (blen == 0)
        diff = 0;
      else
        diff = -1;
    }
  else if (blen == 0)
    {
      diff = 1;
    }
  else if (hard_LC_COLLATE)
    {
      diff = xmemcoll0 (a->text, alen + 1, b->text, blen + 1);
    }
  else
    {
      diff = memcmp (a->text, b->text, MIN (alen, blen));
      if (!diff)
        diff = _GL_CMP (alen, blen);
    }

  return diff_reversed (diff, reverse);
}

/* Write LINE to output stream FP; the output file's name is
   OUTPUT_FILE if OUTPUT_FILE is non-null, and is the standard output
   otherwise.  If debugging is enabled and FP is standard output,
   append some debugging information.  */

static void
write_line (struct line const *line, FILE *fp, char const *output_file)
{
  size_t n_bytes = line->length;

  if (!output_file && debug)
    {
      char const *c = line->text;
      char const *ebuf_debug = line->text + n_bytes;

      while (c < ebuf_debug)
        {
          char wc = *c++;
          if (wc == '\t')
            wc = '>';
          else if (c == ebuf_debug)
            wc = '\n';
          if (fputc (wc, fp) == EOF)
            sort_die (_("write failed"), output_file);
        }

      debug_line (line);
    }
  else
    {
      char *writable_buf = (char *)line->text;
      char *writable_ebuf = writable_buf + n_bytes;

      writable_ebuf[-1] = eolchar;
      if (fwrite (writable_buf, 1, n_bytes, fp) != n_bytes)
        {
          sort_die (_("write failed"), output_file);
        }
      writable_ebuf[-1] = '\0';
    }
}

/* Check that the lines read from FILE_NAME come in order.  Return
   true if they are in order.  If CHECKONLY == 'c', also print a
   diagnostic (FILE_NAME, line number, contents of line) to stderr if
   they are not in order.  */

static bool
check (char const *file_name, char checkonly)
{
  FILE *fp = xfopen (file_name, "r");
  struct buffer buf;
  struct line temp;
  size_t alloc = 0;
  uintmax_t line_number = 0;
  struct keyfield const *key = keylist;
  bool nonunique = ! unique;
  bool ordered = true;

  initbuf (&buf, sizeof (struct line),
           MAX (merge_buffer_size, sort_size));
  temp.text = nullptr;

  while (ordered && fillbuf (&buf, fp, file_name))
    {
      if (buf.nlines == 0)
        continue;

      struct line const *last_in_buffer = buffer_linelim (&buf) - 1;
      struct line const *first_in_buffer = last_in_buffer - buf.nlines + 1;

      if (alloc && nonunique <= compare (&temp, first_in_buffer))
        {
          ordered = false;
          if (checkonly == 'c')
            {
              uintmax_t disorder_line_number = line_number + 1;
              char hr_buf[INT_BUFSIZE_BOUND (disorder_line_number)];
              fprintf (stderr, _("%s: %s:%s: disorder: "),
                       program_name, file_name,
                       umaxtostr (disorder_line_number, hr_buf));
              write_line (first_in_buffer, stderr, _("standard error"));
            }
        }

      if (ordered) {
          struct line const *current_line = last_in_buffer;
          while (current_line > first_in_buffer)
            {
              if (nonunique <= compare (current_line, current_line - 1))
                {
                  ordered = false;
                  if (checkonly == 'c')
                    {
                      uintmax_t disorder_line_number =
                        line_number + (current_line - first_in_buffer + 1);
                      char hr_buf[INT_BUFSIZE_BOUND (disorder_line_number)];
                      fprintf (stderr, _("%s: %s:%s: disorder: "),
                               program_name, file_name,
                               umaxtostr (disorder_line_number, hr_buf));
                      write_line (current_line, stderr, _("standard error"));
                    }
                  break;
                }
              current_line--;
            }
      }

      if (!ordered)
        {
          break;
        }

      line_number += buf.nlines;

      size_t required_length = last_in_buffer->length;
      if (alloc < required_length)
        {
          size_t new_alloc_size = alloc;
          if (new_alloc_size == 0) {
              new_alloc_size = required_length;
          } else {
              if (new_alloc_size > SIZE_MAX / 2) {
                  new_alloc_size = required_length;
              } else {
                  new_alloc_size *= 2;
              }
          }
          if (new_alloc_size < required_length) {
              new_alloc_size = required_length;
          }

          free (temp.text);
          temp.text = xmalloc (new_alloc_size);
          alloc = new_alloc_size;
        }
      memcpy (temp.text, last_in_buffer->text, last_in_buffer->length);
      temp.length = last_in_buffer->length;
      if (key)
        {
          temp.keybeg = temp.text + (last_in_buffer->keybeg - last_in_buffer->text);
          temp.keylim = temp.text + (last_in_buffer->keylim - last_in_buffer->text);
        }
    }

  xfclose (fp, file_name);
  free (buf.buf);
  free (temp.text);
  return ordered;
}

/* Open FILES (there are NFILES of them) and store the resulting array
   of stream pointers into (*PFPS).  Allocate the array.  Return the
   number of successfully opened files, setting errno if this value is
   less than NFILES.  */

static size_t
open_input_files (struct sortfile *files, size_t nfiles, FILE ***pfps)
{
  FILE **fps;
  size_t i;

  fps = xnmalloc (nfiles, sizeof *fps);
  if (!fps)
    {
      *pfps = NULL;
      return 0;
    }
  *pfps = fps;

  for (i = 0; i < nfiles; ++i)
    {
      FILE *current_fp;

      if (files[i].temp && files[i].temp->state != UNCOMPRESSED)
        {
          current_fp = open_temp (files[i].temp);
        }
      else
        {
          current_fp = stream_open (files[i].name, "r");
        }

      if (!current_fp)
        {
          break;
        }

      fps[i] = current_fp;
    }

  return i;
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   FPS is the vector of open stream corresponding to the files.
   Close input and output streams before returning.
   OUTPUT_FILE gives the name of the output file.  If it is null,
   the output file is standard output.  */

static void
remove_initial_file(
    size_t removed_idx, struct sortfile *files_arr, size_t *ntemps_ptr,
    size_t *nfiles_ptr, FILE **fps_arr, struct buffer *buffer_arr)
{
  xfclose(fps_arr[removed_idx], files_arr[removed_idx].name);
  if (removed_idx < *ntemps_ptr)
    {
      (*ntemps_ptr)--;
      zaptemp(files_arr[removed_idx].name);
    }
  free(buffer_arr[removed_idx].buf);

  size_t current_nfiles = *nfiles_ptr;
  for (size_t i = removed_idx; i < current_nfiles - 1; ++i)
    {
      files_arr[i] = files_arr[i + 1];
      fps_arr[i] = fps_arr[i + 1];
      buffer_arr[i] = buffer_arr[i + 1];
    }
  (*nfiles_ptr)--;
}

static void
remove_active_file(
    size_t removed_file_orig_idx,
    struct sortfile *files_arr, size_t *ntemps_ptr, size_t *nfiles_ptr,
    FILE **fps_arr, struct buffer *buffer_arr,
    struct line const **cur_arr, struct line const **base_arr,
    size_t *ord_arr)
{
  size_t current_nfiles = *nfiles_ptr;

  // Adjust indices in the 'ord' array. Any index in 'ord' pointing to a file
  // with an index greater than 'removed_file_orig_idx' needs to be decremented.
  for (size_t i = 0; i < current_nfiles; ++i)
    {
      if (ord_arr[i] > removed_file_orig_idx)
        {
          ord_arr[i]--;
        }
    }

  // Close and cleanup the removed file's resources
  xfclose(fps_arr[removed_file_orig_idx], files_arr[removed_file_orig_idx].name);
  if (removed_file_orig_idx < *ntemps_ptr)
    {
      (*ntemps_ptr)--;
      zaptemp(files_arr[removed_file_orig_idx].name);
    }
  free(buffer_arr[removed_file_orig_idx].buf);

  // Shift arrays to remove the file at removed_file_orig_idx
  for (size_t i = removed_file_orig_idx; i < current_nfiles - 1; ++i)
    {
      files_arr[i] = files_arr[i + 1];
      fps_arr[i] = fps_arr[i + 1];
      buffer_arr[i] = buffer_arr[i + 1];
      cur_arr[i] = cur_arr[i + 1];
      base_arr[i] = base_arr[i + 1];
    }
  (*nfiles_ptr)--; // Decrement total count of active files

  // Shift the 'ord' array itself to remove the element at ord_arr[0]
  // (which referred to the now removed file).
  for (size_t i = 0; i < *nfiles_ptr; ++i)
    {
      ord_arr[i] = ord_arr[i + 1];
    }
}

static void
handle_unique_output(
    struct line const *smallest_line,
    struct line *saved_line_storage,
    struct line const **saved_line_ptr,
    size_t *savealloc_ptr,
    FILE *ofp, char const *output_file_name,
    struct keyfield const *key_list)
{
  // If a line is saved and it's different from the current smallest, output the saved line.
  if (*saved_line_ptr && compare(*saved_line_ptr, smallest_line))
    {
      write_line(*saved_line_ptr, ofp, output_file_name);
      *saved_line_ptr = nullptr; // Clear saved line state
    }

  // If no line is saved (or it was just cleared), save the current smallest line.
  if (!*saved_line_ptr)
    {
      *saved_line_ptr = saved_line_storage; // Point to the storage
      if (*savealloc_ptr < smallest_line->length)
        {
          size_t new_savealloc = *savealloc_ptr;
          if (new_savealloc == 0)
            new_savealloc = smallest_line->length;
          else
            while (new_savealloc < smallest_line->length)
              new_savealloc *= 2; // Double capacity until it fits

          free(saved_line_storage->text);
          saved_line_storage->text = xmalloc(new_savealloc);
          *savealloc_ptr = new_savealloc;
        }
      saved_line_storage->length = smallest_line->length;
      memcpy(saved_line_storage->text, smallest_line->text, smallest_line->length);

      if (key_list)
        {
          saved_line_storage->keybeg =
            saved_line_storage->text + (smallest_line->keybeg - smallest_line->text);
          saved_line_storage->keylim =
            saved_line_storage->text + (smallest_line->keylim - smallest_line->text);
        }
    }
}

static void
initial_sort_ord_array(size_t nfiles, size_t *ord_arr, struct line const **cur_arr)
{
  for (size_t i = 0; i < nfiles; ++i)
    ord_arr[i] = i;

  // This is an O(N^2) stable sort, which ensures ord_arr[0] points to the smallest line.
  for (size_t i = 1; i < nfiles; ++i)
    {
      // If current element is smaller than previous, swap them and restart from beginning
      // to ensure the smallest element bubbles to the front.
      if (0 < compare(cur_arr[ord_arr[i - 1]], cur_arr[ord_arr[i]]))
        {
          size_t temp_val = ord_arr[i - 1];
          ord_arr[i - 1] = ord_arr[i];
          ord_arr[i] = temp_val;
          i = 0; // Restart scan
        }
    }
}

static void
reorder_ord_array(size_t current_nfiles, size_t *ord_arr, struct line const **cur_arr)
{
  size_t ord0_val = ord_arr[0]; // The file index that just had its line advanced.
  size_t lo = 1;
  size_t hi = current_nfiles;
  size_t probe = lo;

  // Binary search to find the correct insertion point for ord0_val, maintaining stability.
  while (lo < hi)
    {
      int cmp = compare(cur_arr[ord0_val], cur_arr[ord_arr[probe]]);
      if (cmp < 0 || (cmp == 0 && ord0_val < ord_arr[probe]))
        hi = probe;
      else
        lo = probe + 1;
      probe = (lo + hi) / 2;
    }

  // Shift elements to make space for ord0_val at its insertion point
  for (size_t j = 0; j < lo - 1; j++)
    ord_arr[j] = ord_arr[j + 1];

  ord_arr[lo - 1] = ord0_val; // Insert ord0_val
}

static void
mergefps (struct sortfile *files, size_t ntemps, size_t nfiles,
          FILE *ofp, char const *output_file, FILE **fps)
{
  // Allocate primary data structures
  struct buffer *buffers = xnmalloc (nfiles, sizeof *buffers);
  struct line const **current_lines = xnmalloc (nfiles, sizeof *current_lines);
  struct line const **base_lines = xnmalloc (nfiles, sizeof *base_lines);
  size_t *ordered_indices = xnmalloc (nfiles, sizeof *ordered_indices);

  struct line saved_line_storage; // For unique check
  saved_line_storage.text = nullptr;
  struct line const *saved_line_pointer = nullptr; // Points to saved_line_storage if active
  size_t saved_line_alloc_size = 0; // Allocated size for saved_line_storage.text

  struct keyfield const *key = keylist; // Assuming keylist is global or passed

  // Read initial lines from each input file
  size_t current_nfiles = nfiles; // Use a mutable copy for file count
  for (size_t i = 0; i < current_nfiles; )
    {
      initbuf (&buffers[i], sizeof (struct line),
               MAX (merge_buffer_size, sort_size / current_nfiles));
      if (fillbuf (&buffers[i], fps[i], files[i].name))
        {
          struct line const *linelim = buffer_linelim (&buffers[i]);
          current_lines[i] = linelim - 1;
          base_lines[i] = linelim - buffers[i].nlines;
          i++; // Successfully read, move to next file
        }
      else
        {
          // fps[i] is empty; eliminate it.
          // Note that `i` is not incremented, so the next iteration will process
          // the file that shifted into position `i`.
          remove_initial_file(i, files, &ntemps, &current_nfiles, fps, buffers);
        }
    }
  nfiles = current_nfiles; // Update nfiles after initial processing

  // Set up the ordered_indices table according to comparisons among initial input lines.
  // This is a stable sort, making ordered_indices[0] point to the smallest line.
  initial_sort_ord_array(nfiles, ordered_indices, current_lines);

  // Repeatedly output the smallest line until no input remains.
  while (nfiles > 0)
    {
      size_t smallest_file_idx = ordered_indices[0];
      struct line const *smallest_line = current_lines[smallest_file_idx];

      if (unique)
        {
          handle_unique_output(smallest_line, &saved_line_storage,
                               &saved_line_pointer, &saved_line_alloc_size,
                               ofp, output_file, key);
        }
      else
        {
          write_line (smallest_line, ofp, output_file);
        }

      // Advance to the next line for the file that provided the smallest.
      if (base_lines[smallest_file_idx] < smallest_line)
        {
          current_lines[smallest_file_idx] = smallest_line - 1;
          // Reorder the ordered_indices table.
          reorder_ord_array(nfiles, ordered_indices, current_lines);
        }
      else
        {
          // Current buffer exhausted, try to fill it again.
          if (fillbuf (&buffers[smallest_file_idx], fps[smallest_file_idx], files[smallest_file_idx].name))
            {
              struct line const *linelim = buffer_linelim (&buffers[smallest_file_idx]);
              current_lines[smallest_file_idx] = linelim - 1;
              base_lines[smallest_file_idx] = linelim - buffers[smallest_file_idx].nlines;
              // Reorder the ordered_indices table.
              reorder_ord_array(nfiles, ordered_indices, current_lines);
            }
          else
            {
              // We reached EOF on this file; eliminate it.
              remove_active_file(smallest_file_idx, files, &ntemps, &nfiles,
                                 fps, buffers, current_lines, base_lines, ordered_indices);
              if (nfiles == 0) break; // All files processed
              continue; // Skip reorder_ord_array, go to next while iteration.
            }
        }
    }

  // Handle any remaining saved line for unique output after the loop finishes.
  if (unique && saved_line_pointer)
    {
      write_line (&saved_line_storage, ofp, output_file);
      free (saved_line_storage.text);
    }

  // Cleanup resources
  xfclose (ofp, output_file); // Final output file close
  free (fps);
  free (buffers);
  free (ordered_indices);
  free (base_lines);
  free (current_lines);
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   Close input and output files before returning.
   OUTPUT_FILE gives the name of the output file.

   Return the number of files successfully merged.  This number can be
   less than NFILES if we ran low on file descriptors, but in this
   case it is never less than 2.  */

static void
cleanup_opened_files_and_array (FILE **fps, size_t n_opened_files)
{
  if (fps)
    {
      for (size_t i = 0; i < n_opened_files; ++i)
        {
          if (fps[i])
            {
              fclose (fps[i]);
            }
        }
      free (fps);
    }
}

static size_t
mergefiles (struct sortfile *files, size_t ntemps, size_t nfiles,
            FILE *ofp, char const *output_file)
{
  FILE **fps = NULL;
  size_t nopened = open_input_files (files, nfiles, &fps);

  if (nopened < 2 && nopened < nfiles)
    {
      cleanup_opened_files_and_array (fps, nopened);
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

  // Merge elements from 'lo' (first source segment) and 'hi' (second source segment)
  // into 't' (destination), working backwards from the end of each segment.
  while (nlo > 0 && nhi > 0)
    {
      // Compare the current elements at the end of each segment (before decrementing pointers).
      if (compare (lo - 1, hi - 1) <= 0)
        {
          // If element from 'lo' is smaller or equal, copy it to 't'.
          *--t = *--lo;
          nlo--;
        }
      else
        {
          // If element from 'hi' is smaller, copy it to 't'.
          *--t = *--hi;
          nhi--;
        }
    }

  // After the main merge loop, one of the source segments is exhausted.

  // If there are remaining elements in 'lo' (the first source segment),
  // copy them to 't'. This typically happens if 'hi' was exhausted first.
  while (nlo > 0)
    {
      *--t = *--lo;
      nlo--;
    }

  // If there are remaining elements in 'hi' (the second source segment),
  // no action is needed. This is because 'hi' points into the 't' buffer itself,
  // meaning these elements are already in their final sorted positions relative
  // to the beginning of the 't' segment.
  // This implicitly handles the case where 'lo' was exhausted first.
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
sequential_sort (struct line *restrict lines_base, size_t nlines,
                 struct line *restrict temp_base, bool to_temp)
{
  if (nlines == 2)
    {
      /* The original code uses lines[-1] and lines[-2].
       * With lines_base pointing to index 0, this translates to
       * lines_base[1] and lines_base[0] respectively.
       * The 'swap' variable definition and usage are preserved to maintain original functionality. */
      int swap_condition = (0 < compare (&lines_base[1], &lines_base[0]));

      if (to_temp)
        {
          /* Original: temp[-1] = lines[-1 - swap]; temp[-2] = lines[-2 + swap];
           * Translated:
           * lines[-1 - swap] becomes lines_base[1 - swap_condition]
           * lines[-2 + swap] becomes lines_base[0 + swap_condition] */
          temp_base[1] = lines_base[1 - swap_condition];
          temp_base[0] = lines_base[0 + swap_condition];
        }
      else if (swap_condition)
        {
          /* Original: temp[-1] = lines[-1]; lines[-1] = lines[-2]; lines[-2] = temp[-1];
           * Using a local scratch variable for the swap to avoid potential side effects
           * or ambiguity with the 'temp_base' array which is also a function parameter.
           * This improves reliability. */
          struct line scratch = lines_base[1];
          lines_base[1] = lines_base[0];
          lines_base[0] = scratch;
        }
    }
  else
    {
      size_t nlo = nlines / 2;     /* Number of elements in the lower half */
      size_t nhi = nlines - nlo;   /* Number of elements in the upper half */

      /* First recursive call: Sort the upper half.
       * Original call: sequential_sort (hi, nhi, temp - (to_temp ? nlo : 0), to_temp);
       * 'hi' in original logic refers to 'lines - nlo'.
       * With 'lines_base' (ptr to first element), this is 'lines_base + nlo'.
       * The 'temp' argument also needs to be adjusted.
       * If 'to_temp' is true for the current call, the upper half uses its own segment
       * within 'temp_base', starting at 'temp_base + nlo'.
       * If 'to_temp' is false, it uses the entire 'temp_base' for auxiliary. */
      sequential_sort (lines_base + nlo, nhi, temp_base + (to_temp ? nlo : 0), to_temp);

      /* Second recursive call: Sort the lower half.
       * Original call: if (1 < nlo) sequential_sort (lo, nlo, temp, !to_temp);
       * 'lo' in original logic refers to 'lines'.
       * With 'lines_base' (ptr to first element), this is 'lines_base'.
       * The 'temp' argument is 'temp_base' (the entire auxiliary buffer for the sub-sort).
       * The '!to_temp' flag indicates the result of this sub-sort should go into the 'lines_base' segment itself
       * (using 'temp_base' as auxiliary for internal operations of the sub-sort). */
      if (1 < nlo)
        sequential_sort (lines_base, nlo, temp_base, !to_temp);
      else if (!to_temp)
        {
          /* Original: temp[-1] = lo[-1];
           * If nlo == 1, the lower half has only one element.
           * 'lo[-1]' refers to the single element: 'lines_base[0]'.
           * 'temp[-1]' refers to 'temp_base[0]' if the temp buffer for this sub-call also has only 1 element.
           * Given the context of the merge, if !to_temp for the parent call,
           * the element from lines_base[0] needs to be copied to temp_base[0]
           * so that mergelines can correctly find both halves. */
          temp_base[0] = lines_base[0];
        }

      /* Merge step
       * The mergelines function (not provided) is assumed to handle the merge
       * according to its original contract, which implied it could derive
       * the two sorted sub-arrays from 'dest' and 'source_base' and the 'nlines' parameter. */
      struct line *dest_base;
      struct line const *source_base_for_halves;

      if (to_temp)
        {
          /* Merge 'lines_base' (lower half sorted in-place) and 'temp_base + nlo' (upper half sorted to temp)
           * into 'temp_base' (final destination).
           * 'mergelines' is assumed to find the other sorted half from 'source_base_for_halves' and 'nlines'. */
          dest_base = temp_base;
          source_base_for_halves = lines_base;
        }
      else
        {
          /* Merge 'temp_base' (lower half sorted to temp) and 'temp_base + nlo' (upper half sorted to temp)
           * into 'lines_base' (final destination).
           * 'mergelines' is assumed to find both sorted halves from 'source_base_for_halves' and 'nlines'. */
          dest_base = lines_base;
          source_base_for_halves = temp_base;
        }
      mergelines (dest_base, nlines, source_base_for_halves);
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
  struct merge_node *merge_tree = xmalloc (2 * sizeof *merge_tree * nthreads);
  struct merge_node *root = merge_tree;

  root->parent = nullptr;
  root->level = MERGE_END;
  root->queued = false;

  if (pthread_mutex_init (&root->lock, nullptr) != 0)
    {
      free (merge_tree);
      return nullptr;
    }

  init_node (root, root + 1, dest, nthreads, nlines, false);
  return merge_tree;
}

/* Destroy the merge tree. */
static void
merge_tree_destroy (size_t nthreads, struct merge_node *merge_tree)
{
  if (merge_tree == NULL)
    {
      /* Nothing to destroy if the tree itself is NULL.
       * free(NULL) is a no-op, but we avoid potential
       * dereferences in the loop if nthreads > 0. */
      return;
    }

  const size_t num_nodes = nthreads * 2;

  /* Iterate through each node to destroy its mutex.
   * A for loop is generally preferred for clarity when iterating
   * a known number of times using an index. */
  for (size_t i = 0; i < num_nodes; ++i)
    {
      /* pthread_mutex_destroy can return an error, but in cleanup
       * functions like this, it's common practice to ignore it,
       * as the program state is often unrecoverable or exiting. */
      pthread_mutex_destroy (&merge_tree[i].lock);
    }

  /* Free the memory allocated for the merge tree. */
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
           const struct line *restrict dest, const size_t nthreads,
           const size_t total_lines, const bool is_lo_child)
{
  // Calculate sizes for this node's segments based on parent's segments.
  // This function assumes 'parent' is never NULL, as 'parent->nlo' and 'parent->nhi' are accessed.
  const size_t nlines = (is_lo_child ? parent->nlo : parent->nhi);
  const size_t nlo = nlines / 2;
  const size_t nhi = nlines - nlo;

  // Calculate the start pointers for this node's 'lo' and 'hi' segments.
  // The interpretation of 'dest' and 'total_lines' for pointer arithmetic is preserved
  // as per the original functionality.
  struct line *lo_segment_start = (struct line *)(dest - total_lines);
  struct line *hi_segment_start = (struct line *)(lo_segment_start - nlo);

  // Determine which pointer in the parent node this node's merged output will update.
  struct line **parent_dest_ptr = (is_lo_child ? &parent->end_lo : &parent->end_hi);

  // Get the current node from the pre-allocated pool and advance the pool pointer for the next allocation.
  struct merge_node *node = node_pool++;

  // Initialize all fields of the current node.
  // Note: node->end_lo and node->end_hi are initialized to the same value as node->lo and node->hi.
  // This behavior is maintained from the original code.
  node->lo = node->end_lo = lo_segment_start;
  node->hi = node->end_hi = hi_segment_start;
  node->dest = parent_dest_ptr;
  node->nlo = nlo;
  node->nhi = nhi;
  node->parent = parent;
  node->level = parent->level + 1;
  node->queued = false;

  // Initialize the Pthread mutex for this node.
  // Proper error handling is essential to prevent undefined behavior if mutex initialization fails.
  int mutex_init_result = pthread_mutex_init(&node->lock, NULL);
  if (mutex_init_result != 0)
    {
      // If mutex initialization fails, it's a critical error that prevents the node from functioning correctly.
      // Given the function's return type and implicit contract (always returning an advanced node_pool pointer),
      // graceful error propagation through the return value is not directly supported without altering external functionality.
      // Terminating the program explicitly ensures that the issue is not silently ignored, preventing
      // subsequent use of an uninitialized mutex which would lead to crashes or undefined behavior.
      fprintf(stderr, "Fatal Error: Failed to initialize mutex for merge_node (error code: %d).\n", mutex_init_result);
      exit(EXIT_FAILURE);
    }

  // Recursively initialize child nodes if there are enough threads to divide the work.
  if (nthreads > 1)
    {
      const size_t lo_threads = nthreads / 2;
      const size_t hi_threads = nthreads - lo_threads;

      // Initialize the low child node.
      // node_pool is updated by the recursive call to point to the next available slot.
      node->lo_child = node_pool;
      node_pool = init_node(node, node_pool, lo_segment_start, lo_threads,
                            total_lines, true);

      // Initialize the high child node.
      // node_pool is again updated by the recursive call.
      node->hi_child = node_pool;
      node_pool = init_node(node, node_pool, hi_segment_start, hi_threads,
                            total_lines, false);
    }
  else
    {
      // Base case: If only one thread (or fewer) is available, this node has no children.
      node->lo_child = NULL;
      node->hi_child = NULL;
    }

  // Return the updated node_pool pointer, indicating the next available slot
  // after this node and its entire subtree have been initialized.
  return node_pool;
}


/* Compare two merge nodes A and B for priority.  */

static int
compare_nodes (void const *a, void const *b)
{
  struct merge_node const *nodea = (struct merge_node const *)a;
  struct merge_node const *nodeb = (struct merge_node const *)b;

  // Primary comparison: 'level'
  // Return -1 if nodea->level < nodeb->level
  // Return 1 if nodea->level > nodeb->level
  // Continue if nodea->level == nodeb->level (return 0)
  if (nodea->level < nodeb->level)
  {
    return -1;
  }
  if (nodea->level > nodeb->level)
  {
    return 1;
  }

  // If levels are equal, proceed to secondary comparison: (nlo + nhi)
  // Use long long for sums to prevent potential integer overflow during calculation,
  // enhancing reliability, especially if nlo and nhi can be large integers.
  long long sum_a = (long long)nodea->nlo + nodea->nhi;
  long long sum_b = (long long)nodeb->nlo + nodeb->nhi;

  if (sum_a < sum_b)
  {
    return -1;
  }
  if (sum_a > sum_b)
  {
    return 1;
  }

  // If both levels and sums are equal, the nodes are considered equivalent.
  return 0;
}

/* Lock a merge tree NODE.  */

static inline void
lock_node (struct merge_node *node)
{
  if (node == NULL)
    {
      /*
       * Critical error: Attempting to lock a NULL node.
       * This indicates a severe programming error or memory corruption.
       * Aborting prevents a segfault (undefined behavior) and ensures the program fails
       * loudly and immediately, improving reliability and security.
       */
      abort();
    }

  int result = pthread_mutex_lock (&node->lock);

  if (result != 0)
    {
      /*
       * Critical error: pthread_mutex_lock failed.
       * This can happen due to various reasons (e.g., deadlocks, invalid mutex).
       * Ignoring the return value is a common code smell and reliability issue.
       * Aborting ensures the program does not proceed with an unacquired lock,
       * preventing potential data corruption, race conditions, or inconsistent states.
       * In a more sophisticated system, this error might be logged with its reason
       * (e.g., using strerror(result)) before aborting.
       */
      abort();
    }
}

/* Unlock a merge tree NODE. */

#include <assert.h>

static inline void
unlock_node (struct merge_node *node)
{
  assert(node != NULL);
  int result = pthread_mutex_unlock(&node->lock);
  assert(result == 0);
}

/* Destroy merge QUEUE. */

static void
queue_destroy (struct merge_node_queue *queue)
{
  if (queue == NULL)
    {
      return;
    }

  heap_free (queue->priority_queue);
  pthread_cond_destroy (&queue->cond);
  pthread_mutex_destroy (&queue->mutex);
}

/* Initialize merge QUEUE, allocating space suitable for a maximum of
   NTHREADS threads.  */

static int
queue_init (struct merge_node_queue *queue, size_t nthreads)
{
  int ret;

  if (queue == NULL)
    {
      return EINVAL; /* Invalid argument */
    }

  queue->priority_queue = heap_alloc (compare_nodes, 2 * nthreads);
  if (queue->priority_queue == NULL)
    {
      return ENOMEM; /* Memory allocation failed */
    }

  ret = pthread_mutex_init (&queue->mutex, NULL);
  if (ret != 0)
    {
      heap_free(queue->priority_queue);
      queue->priority_queue = NULL; /* Mark as unallocated */
      return ret;
    }

  ret = pthread_cond_init (&queue->cond, NULL);
  if (ret != 0)
    {
      pthread_mutex_destroy(&queue->mutex);
      heap_free(queue->priority_queue);
      queue->priority_queue = NULL; /* Mark as unallocated */
      return ret;
    }

  return 0; /* Success */
}

/* Insert NODE into QUEUE.  The caller either holds a lock on NODE, or
   does not need to lock NODE.  */

static int
queue_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (queue == NULL || node == NULL) {
    return EINVAL;
  }

  int ret = 0;
  int lock_res = pthread_mutex_lock(&queue->mutex);
  if (lock_res != 0) {
    return lock_res;
  }

  heap_insert(queue->priority_queue, node);
  node->queued = true;

  int signal_res = pthread_cond_signal(&queue->cond);
  int unlock_res = pthread_mutex_unlock(&queue->mutex);

  if (unlock_res != 0) {
    ret = unlock_res;
  } else if (signal_res != 0) {
    ret = signal_res;
  }

  return ret;
}

/* Pop the top node off the priority QUEUE, lock the node, return it.  */

static struct merge_node *
queue_pop (struct merge_node_queue *queue)
{
  struct merge_node *node;

  pthread_mutex_lock(&queue->mutex);

  while (!(node = heap_remove_top(queue->priority_queue)))
    pthread_cond_wait(&queue->cond, &queue->mutex);

  node->queued = false; /* Ensure node state update is within queue's critical section */

  pthread_mutex_unlock(&queue->mutex);

  lock_node(node); /* Node-specific lock, separate from queue's mutex */

  return node;
}

/* Output LINE to TFP, unless -u is specified and the line compares
   equal to the previous line.  TEMP_OUTPUT is the name of TFP, or
   is null if TFP is standard output.

   This function does not save the line for comparison later, so it is
   appropriate only for internal sort.  */

#include <stdbool.h>
#include <stdio.h>

/* Assuming the following are declared elsewhere, e.g., in a header file:
 *
 * struct line {
 *   char *text;
 *   // ... other members relevant for comparison/writing
 * };
 *
 * // Returns 0 if lines are identical, non-zero otherwise.
 * extern int compare(struct line const *line1, struct line const *line2);
 *
 * // Writes a line to the file. Returns 0 on success, non-zero on failure.
 * extern int write_line(struct line const *line, FILE *tfp, char const *temp_output_path);
 */

static int
write_unique (struct line const *current_line, FILE *tfp, char const *temp_output_path,
              bool is_unique_mode, struct line *last_written_line_state)
{
  if (is_unique_mode)
    {
      if (last_written_line_state->text != NULL && compare(current_line, last_written_line_state) == 0)
        {
          return 0; // Successfully skipped an identical line
        }
      *last_written_line_state = *current_line; // Shallow copy of the line state
    }

  return write_line(current_line, tfp, temp_output_path);
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
  struct line *lo_start_ptr = node->lo;
  struct line *hi_start_ptr = node->hi;
  size_t merge_limit = MAX_MERGE (total_lines, node->level);
  size_t lines_merged_count = 0;

  if (node->level > MERGE_ROOT)
    {
      /* Merge to destination buffer. */
      struct line *dest_ptr = *node->dest;

      /* Main merge loop: while both lists have elements AND limit not reached. */
      while (node->lo != node->end_lo && node->hi != node->end_hi && lines_merged_count < merge_limit)
        {
          if (compare (node->lo - 1, node->hi - 1) <= 0)
            *--dest_ptr = *--node->lo;
          else
            *--dest_ptr = *--node->hi;
          lines_merged_count++;
        }

      /* After the main loop, one of the lists might be exhausted or the merge limit reached. */
      /* Drain remaining 'lo' lines if 'hi' was exhausted (or initially empty) AND limit not reached. */
      if (node->hi == node->end_hi)
        {
          while (node->lo != node->end_lo && lines_merged_count < merge_limit)
            {
              *--dest_ptr = *--node->lo;
              lines_merged_count++;
            }
        }
      /* Drain remaining 'hi' lines if 'lo' was exhausted (or initially empty) AND limit not reached. */
      else if (node->lo == node->end_lo)
        {
          while (node->hi != node->end_hi && lines_merged_count < merge_limit)
            {
              *--dest_ptr = *--node->hi;
              lines_merged_count++;
            }
        }
      *node->dest = dest_ptr;
    }
  else /* node->level <= MERGE_ROOT */
    {
      /* Merge directly to output. */

      /* Main merge loop: while both lists have elements AND limit not reached. */
      while (node->lo != node->end_lo && node->hi != node->end_hi && lines_merged_count < merge_limit)
        {
          if (compare (node->lo - 1, node->hi - 1) <= 0)
            write_unique (--node->lo, tfp, temp_output);
          else
            write_unique (--node->hi, tfp, temp_output);
          lines_merged_count++;
        }

      /* Drain remaining 'lo' lines if 'hi' was exhausted (or initially empty) AND limit not reached. */
      if (node->hi == node->end_hi)
        {
          while (node->lo != node->end_lo && lines_merged_count < merge_limit)
            {
              write_unique (--node->lo, tfp, temp_output);
              lines_merged_count++;
            }
        }
      /* Drain remaining 'hi' lines if 'lo' was exhausted (or initially empty) AND limit not reached. */
      else if (node->lo == node->end_lo)
        {
          while (node->hi != node->end_hi && lines_merged_count < merge_limit)
            {
              write_unique (--node->hi, tfp, temp_output);
              lines_merged_count++;
            }
        }
    }

  /* Update NODE counts based on consumed lines. */
  node->nlo -= (lo_start_ptr - node->lo);
  node->nhi -= (hi_start_ptr - node->hi);
}

/* Into QUEUE, insert NODE if it is not already queued, and if one of
   NODE's children has available lines and the other either has
   available lines or has exhausted its lines.  */

static void
queue_check_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (node == NULL)
    {
      return;
    }

  if (!node->queued)
    {
      bool lo_avail = (node->lo - node->end_lo) != 0;
      bool hi_avail = (node->hi - node->end_hi) != 0;

      bool should_insert = false;
      if (lo_avail)
        {
          should_insert = hi_avail || !node->nhi;
        }
      else
        {
          should_insert = hi_avail && !node->nlo;
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
  if (node->level > MERGE_ROOT)
    {
      if (node->parent != NULL)
        {
          lock_node (node->parent);
          queue_check_insert (queue, node->parent);
          unlock_node (node->parent);
        }
    }
  else if (node->nlo + node->nhi == 0)
    {
      if (node->parent != NULL)
        {
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
  bool running = true;
  while (running)
    {
      struct merge_node *node = queue_pop (queue);

      if (node->level == MERGE_END)
        {
          unlock_node (node);
          queue_insert (queue, node);
          running = false;
        }
      else
        {
          mergelines_node (node, total_lines, tfp, temp_output);
          queue_check_insert (queue, node);
          queue_check_insert_parent (queue, node);
          unlock_node (node);
        }
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

#include <stddef.h>

static void *
sortlines_thread (void *data)
{
  struct thread_args const *args = (struct thread_args const *)data;

  if (args == NULL) {
    return NULL;
  }

  sortlines (args->lines, args->nthreads, args->total_lines,
             args->node, args->queue, args->tfp,
             args->output_temp);

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
  size_t const current_segment_nlines = node->nlo + node->nhi;

  /* Calculate thread arguments. */
  size_t const lo_threads = nthreads / 2;
  size_t const hi_threads = nthreads - lo_threads;

  struct thread_args args = {
      .lines = lines,
      .nthreads = lo_threads,
      .total_lines = total_lines,
      .node = node->lo_child,
      .queue = queue,
      .tfp = tfp,
      .temp_output = temp_output
  };

  if (nthreads > 1 && SUBTHREAD_LINES_HEURISTIC <= current_segment_nlines)
    {
      pthread_t thread_handle;
      int const create_status = pthread_create(&thread_handle, NULL, sortlines_thread, &args);

      if (create_status == 0)
        {
          sortlines(lines - node->nlo, hi_threads, total_lines,
                    node->hi_child, queue, tfp, temp_output);
          pthread_join(thread_handle, NULL);
        }
      else
        {
          goto sequential_sort_path;
        }
    }
  else
    {
    sequential_sort_path:;
      size_t const nlo = node->nlo;
      size_t const nhi = node->nhi;
      
      struct line *const temp_buffer_base = lines - total_lines;

      if (nhi >= 2)
        sequential_sort(lines - nlo, nhi, temp_buffer_base - nlo / 2, false);
      if (nlo >= 2)
        sequential_sort(lines, nlo, temp_buffer_base, false);

      node->lo = lines;
      node->hi = lines - nlo;
      node->end_lo = lines - nlo;
      node->end_hi = lines - nlo - nhi;

      queue_insert(queue, node);
      merge_loop(queue, total_lines, tfp, temp_output);
    }
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

static void
avoid_trashing_input (struct sortfile *files, size_t ntemps,
                      size_t nfiles, char const *outfile)
{
  for (size_t i = ntemps; i < nfiles; i++)
    {
      bool is_stdin = STREQ (files[i].name, "-");
      bool same = false;

      if (outfile && STREQ (outfile, files[i].name) && !is_stdin)
        {
          same = true;
        }
      else
        {
          struct stat *outst = get_outstatus ();
          if (outst == NULL)
            {
              break;
            }

          struct stat instat;
          if ((is_stdin
                ? fstat (STDIN_FILENO, &instat)
                : stat (files[i].name, &instat)) == 0)
            {
              same = psame_inode (&instat, outst);
            }
        }

      if (same)
        {
          struct tempnode *current_temp_node = NULL;
          FILE *temp_file_stream = NULL;

          current_temp_node = create_temp (&temp_file_stream);

          if (current_temp_node == NULL || temp_file_stream == NULL)
            {
              break;
            }

          mergefiles (&files[i], 0, 1, temp_file_stream, current_temp_node->name);

          (void) fclose(temp_file_stream);

          files[i].name = current_temp_node->name;
          files[i].temp = current_temp_node;
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
      if (strcmp(files[i], "-") == 0)
        {
          continue;
        }

      if (euidaccess (files[i], R_OK) != 0)
        {
          sort_die (_("cannot read"), files[i]);
        }
    }
}

/* Ensure a specified output file can be created or written to,
   and point stdout to it.  Do not truncate the file.
   Exit with a diagnostic on failure.  */

static void
check_output (char const *outfile)
{
  if (outfile)
    {
      int oflags = O_WRONLY | O_BINARY | O_CLOEXEC | O_CREAT;
      int outfd = open (outfile, oflags, MODE_RW_UGO);
      if (outfd < 0)
        sort_die (_("open failed"), outfile);

      if (move_fd (outfd, STDOUT_FILENO) < 0)
        {
          /* If move_fd fails, the original 'outfd' is still open.
           * Close it to prevent a resource leak before exiting. */
          int saved_errno = errno;
          close (outfd);
          errno = saved_errno; /* Restore errno for sort_die to use */
          sort_die (_("failed to redirect output"), outfile);
        }
    }
}

/* Merge the input FILES.  NTEMPS is the number of files at the
   start of FILES that are temporary; it is zero at the top level.
   NFILES is the total number of files.  Put the output in
   OUTPUT_FILE; a null OUTPUT_FILE stands for standard output.  */

#define MIN(a, b) (((a) < (b)) ? (a) : (b))

static void
merge (struct sortfile *files, size_t ntemps, size_t nfiles,
       char const *output_file)
{
  /* Assume `nmerge` is an externally defined global or static size_t variable
     representing the maximum number of files to merge in a single batch (fan-in limit).
     It also acts as a threshold for the iterative merging passes. Its value is
     expected to be set prior to calling this function. */

  /* Define constants for readability and maintainability within this function. */
  /* These values (2) are hard-coded in the original logic, assuming they are
     critical thresholds for file descriptor management. */
#define MIN_FILES_FOR_FINAL_ATTEMPT 2
#define CRITICAL_FD_THRESHOLD       2

  /* First phase: Multi-way merge passes until nfiles is small enough (<= nmerge). */
  while (nmerge < nfiles)
    {
      size_t current_input_idx = 0;   /* Index for reading from the current `files` array. */
      size_t current_output_idx = 0;  /* Index for writing to the `files` array (new temporaries). */
      size_t files_for_this_pass = nfiles; /* Total input files for this specific pass. */

      /* Perform as many full 'nmerge'-sized merges as possible.
         The loop continues as long as there are enough remaining files
         (files_for_this_pass - current_input_idx) to form a complete batch of 'nmerge'. */
      for (current_output_idx = 0, current_input_idx = 0;
           current_input_idx <= files_for_this_pass - nmerge;
           current_output_idx++)
        {
          FILE *temp_output_fp;
          /* create_temp is assumed to handle errors internally, potentially via sort_die. */
          struct tempnode *temp_node = create_temp (&temp_output_fp);
          /* Defensive check, though create_temp might be designed to never return NULL. */
          if (!temp_node)
            sort_die (_("failed to create temporary file"), output_file);

          size_t files_merged_in_batch = mergefiles (&files[current_input_idx],
                                                      MIN (ntemps, nmerge),
                                                      nmerge, temp_output_fp, temp_node->name);

          /* Update counts for the current merge pass. */
          ntemps -= MIN (ntemps, files_merged_in_batch);
          files[current_output_idx].name = temp_node->name;
          files[current_output_idx].temp = temp_node;
          current_input_idx += files_merged_in_batch;
        }

      /* Handle any remaining input files that couldn't form a full 'nmerge'-sized batch. */
      size_t remaining_unmerged_inputs = files_for_this_pass - current_input_idx;
      size_t available_output_slots_in_window = nmerge - (current_output_idx % nmerge);

      if (available_output_slots_in_window < remaining_unmerged_inputs)
        {
          /* There are more remaining input files than can fit into the current
             logical output window without exceeding 'nmerge' files in total.
             Perform one additional, smaller merge to balance the workload for the next pass. */
          size_t short_merge_batch_size = remaining_unmerged_inputs - available_output_slots_in_window + 1;
          FILE *temp_output_fp;
          struct tempnode *temp_node = create_temp (&temp_output_fp);
          if (!temp_node)
            sort_die (_("failed to create temporary file"), output_file);

          size_t files_merged_in_batch = mergefiles (&files[current_input_idx],
                                                      MIN (ntemps, short_merge_batch_size),
                                                      short_merge_batch_size, temp_output_fp, temp_node->name);

          ntemps -= MIN (ntemps, files_merged_in_batch);
          files[current_output_idx].name = temp_node->name;
          files[current_output_idx++].temp = temp_node;
          current_input_idx += files_merged_in_batch;
        }

      /* Move any truly remaining, unmerged input files to their new positions
         at the end of the `files` array. These files will be processed in the next pass. */
      memmove (&files[current_output_idx], &files[current_input_idx],
               (files_for_this_pass - current_input_idx) * sizeof *files);

      /* Update the global file counts for the next pass. */
      ntemps += current_output_idx; /* The new temporary files become inputs for the next pass. */
      nfiles -= (current_input_idx - current_output_idx); /* Adjust `nfiles` to reflect new number of merge units. */
    }

  avoid_trashing_input (files, ntemps, nfiles, output_file);

  /* Second phase: Final merge into the output file, with file descriptor recovery if needed. */
  while (true)
    {
      FILE **input_file_pointers = NULL;
      size_t num_successfully_opened_inputs = open_input_files (files, nfiles, &input_file_pointers);

      if (num_successfully_opened_inputs == nfiles)
        {
          /* All input files were successfully opened. Attempt to open the output file. */
          FILE *output_stream = stream_open (output_file, "w");
          if (output_stream)
            {
              /* All files are open; proceed with the final merge. */
              mergefps (files, ntemps, nfiles, output_stream, output_file, input_file_pointers);
              break; /* Success: exit the final merge loop. */
            }

          /* If output file opening failed: check for EMFILE or critical FD shortage. */
          if (errno != EMFILE || nfiles <= MIN_FILES_FOR_FINAL_ATTEMPT)
            {
              /* Not an EMFILE error, or too few files to recover from;
                 this is a critical failure. */
              sort_die (_("failed to open output file"), output_file);
            }
          /* If it's EMFILE and there are enough files, fall through to FD recovery. */
        }
      else if (num_successfully_opened_inputs <= CRITICAL_FD_THRESHOLD)
        {
          /* Critical failure: Unable to open even a minimal set of input files. */
          /* The error message points to the first file that failed to open. */
          sort_die (_("failed to open input file"), files[num_successfully_opened_inputs].name);
        }

      /* File descriptor shortage: We couldn't open all necessary files (either input or output file).
         Initiate recovery by closing some input files, creating a temporary file,
         and merging a subset of the inputs into it. */

      struct tempnode *temp_output_node = NULL;
      FILE *temp_output_fp = NULL;
      /* Start with the count of currently opened input files. */
      size_t inputs_for_current_temp_merge = num_successfully_opened_inputs;

      /* Repeatedly close one input file and attempt to create a temporary file.
         This loop continues until a temporary file can be created, or until
         the number of available file descriptors drops below a critical threshold. */
      do
        {
          if (inputs_for_current_temp_merge == 0)
            {
              /* No more input files to close to free descriptors; critical failure. */
              sort_die (_("critical file descriptor shortage, cannot proceed"), output_file);
            }
          inputs_for_current_temp_merge--;
          /* Close the last opened input file to free a descriptor. */
          xfclose (input_file_pointers[inputs_for_current_temp_merge],
                   files[inputs_for_current_temp_merge].name);

          /* Attempt to create a temporary file. The second argument to maybe_create_temp
             indicates if it's acceptable to `sort_die` on failure (if not in a critical FD situation). */
          temp_output_node = maybe_create_temp (&temp_output_fp,
                                                 !(inputs_for_current_temp_merge <= CRITICAL_FD_THRESHOLD));
        }
      while (!temp_output_node && inputs_for_current_temp_merge > 0);

      if (!temp_output_node)
        {
          /* If the loop exited without creating a temporary file (e.g., inputs_for_current_temp_merge became 0). */
          sort_die (_("cannot create temporary file due to severe file descriptor shortage"), output_file);
        }

      /* Merge the subset of opened input files into the newly created temporary file. */
      mergefps (&files[0],
                MIN (ntemps, inputs_for_current_temp_merge),
                inputs_for_current_temp_merge,
                temp_output_fp,
                temp_output_node->name,
                input_file_pointers); /* input_file_pointers array is now partially closed. */

      /* Update the `files` array: the new temporary file replaces the merged inputs. */
      ntemps -= MIN (ntemps, inputs_for_current_temp_merge);
      files[0].name = temp_output_node->name;
      files[0].temp = temp_output_node;

      /* Shift the remaining unmerged input files to follow the new temporary file. */
      memmove (&files[1],
               &files[inputs_for_current_temp_merge],
               (nfiles - inputs_for_current_temp_merge) * sizeof *files);

      ntemps++; /* One new temporary file was created. */
      nfiles -= (inputs_for_current_temp_merge - 1); /* Number of merge units reduced. */
    }
#undef MIN_FILES_FOR_FINAL_ATTEMPT
#undef CRITICAL_FD_THRESHOLD
}

/* Sort NFILES FILES onto OUTPUT_FILE.  Use at most NTHREADS threads.  */

static void
sort (char *const *files, size_t nfiles, char const *output_file,
      size_t nthreads)
{
  struct buffer buf;
  size_t ntemps = 0;
  FILE *current_input_fp = NULL;
  char const *current_input_file_name = NULL;
  size_t initial_nfiles = nfiles;

  // Calculate bytes_per_line once, based on nthreads.
  // This logic is preserved from the original code.
  size_t bytes_per_line;
  if (nthreads > 1)
    {
      size_t tmp_val = 1;
      size_t mult_val = 1;
      while (tmp_val < nthreads)
        {
          tmp_val *= 2;
          mult_val++;
        }
      bytes_per_line = (mult_val * sizeof (struct line));
    }
  else
    {
      bytes_per_line = sizeof (struct line) * 3 / 2;
    }

  // Explicitly mark buffer as unallocated to ensure one-time initialization.
  buf.alloc = 0;
  bool direct_output_finalized = false; // Controls direct writing to output_file

  // Iterate through all input files.
  for (size_t file_idx = 0; file_idx < initial_nfiles; ++file_idx)
    {
      // If the final output has already been written directly,
      // skip processing any remaining input files.
      if (direct_output_finalized)
        {
          break;
        }

      current_input_file_name = files[file_idx];
      current_input_fp = xfopen (current_input_file_name, "r");

      // Initialize buffer only once using the context of the first opened file.
      if (!buf.alloc)
        {
          initbuf (&buf, bytes_per_line,
                   sort_buffer_size (&current_input_fp, initial_nfiles - file_idx,
                                     files + file_idx, initial_nfiles - file_idx,
                                     bytes_per_line));
        }
      buf.eof = false; // Reset EOF flag for each new input file.

      // Inner loop: fill buffer and process its contents chunk by chunk.
      while (fillbuf (&buf, current_input_fp, current_input_file_name))
        {
          // Check for buffer concatenation opportunity:
          // If at the end of the current file, more input files are available,
          // and there's enough room in the buffer to concatenate.
          if (buf.eof && (file_idx + 1 < initial_nfiles)
              && (bytes_per_line + 1
                  < (buf.alloc - buf.used - bytes_per_line * buf.nlines)))
            {
              buf.left = buf.used; // Mark current data as 'left' for next fillbuf call to append.
              break; // Break inner loop, move to the next input file.
            }

          FILE *output_fp = NULL;
          char const *temp_output_name = NULL;

          // Determine if this chunk should be written directly to the final output file,
          // or to a temporary file. This happens if it's the very last chunk
          // of the very last input file, and no temporary files have been created yet.
          if (buf.eof && (file_idx + 1 == initial_nfiles) && (ntemps == 0) && (buf.left == 0))
            {
              output_fp = xfopen (output_file, "w");
              temp_output_name = output_file;
              direct_output_finalized = true;
            }
          else
            {
              ++ntemps;
              struct tempnode *temp_node = create_temp (&output_fp);
              // x-functions are assumed to handle their own error conditions (e.g., exit).
              temp_output_name = temp_node->name;
            }

          // Get pointer to the first line in the buffer chunk.
          struct line *line = buffer_linelim (&buf);

          // If there's more than one line in the buffer chunk, sort them.
          if (buf.nlines > 1)
            {
              struct merge_node_queue queue;
              queue_init (&queue, nthreads);
              struct merge_node *merge_tree = merge_tree_init (nthreads, buf.nlines, line);

              sortlines (line, nthreads, buf.nlines, merge_tree + 1,
                         &queue, output_fp, temp_output_name);

              merge_tree_destroy (nthreads, merge_tree);
              queue_destroy (&queue);
            }
          else // Only one line in buffer chunk, write it directly.
            {
              // The original code uses 'line - 1'. Preserving this behavior.
              write_unique (line - 1, output_fp, temp_output_name);
            }

          xfclose (output_fp, temp_output_name); // Close the output file (temp or final).

          // If final output was written directly, we are done.
          if (direct_output_finalized)
            {
              xfclose (current_input_fp, current_input_file_name);
              current_input_fp = NULL; // Mark as closed to prevent double-close.
              break; // Exit inner loop.
            }
        }
      // Ensure the current input file is closed if not already closed by direct_output_finalized path.
      if (current_input_fp)
        {
          xfclose (current_input_fp, current_input_file_name);
          current_input_fp = NULL;
        }
    }

  // --- Cleanup and final merge phase ---

  free (buf.buf); // Free the main buffer's allocated memory.

  // If the final output was not written directly, it means temporary files were created
  // and need to be merged.
  if (!direct_output_finalized)
    {
      struct tempnode *node = temphead; // Assumed global head of temp file linked list.
      struct sortfile *tempfiles = NULL;

      if (ntemps > 0)
        {
          tempfiles = xnmalloc (ntemps, sizeof (*tempfiles));
          // xnmalloc is assumed to handle allocation failures by exiting.
          for (size_t k = 0; k < ntemps && node; ++k)
            {
              tempfiles[k].name = node->name;
              tempfiles[k].temp = node;
              node = node->next;
            }
          // Merge the temporary files into the final output file.
          merge (tempfiles, ntemps, ntemps, output_file);
          free (tempfiles);
        }
    }

  reap_all (); // Clean up all temporary files created during the process.
}

/* Insert a malloc'd copy of key KEY_ARG at the end of the key list.  */

static void
insertkey (const struct keyfield *key_arg)
{
  struct keyfield **p = &keylist;
  struct keyfield *key = xmemdup (key_arg, sizeof *key_arg);

  while (*p != nullptr) {
    p = &(*p)->next;
  }
  *p = key;
  key->next = nullptr;
}

/* Report a bad field specification SPEC, with extra info MSGID.  */

static void
badfieldspec (char const *spec, char const *msgid)
{
  char const *localized_msgid = _(msgid);
  char const *quoted_spec_str = quote(spec);

  error (SORT_FAILURE, 0, _("%s: invalid field specification %s"),
         localized_msgid ? localized_msgid : "(null)",
         quoted_spec_str ? quoted_spec_str : "(null)");
}

/* Report incompatible options.  */

static void
incompatible_options (char const *opts)
{
  error (SORT_FAILURE, 0, _("options '-%s' are incompatible"), opts);
}

/* Check compatibility of ordering options.  */

static void
check_ordering_compatibility (void)
{
  struct keyfield *key;

  for (key = keylist; key; key = key->next)
    {
      /* Calculate a score based on combined key properties.
         This computation precisely preserves the original logic,
         including potential contributions greater than 1 from bitwise OR operations. */
      int combined_key_score = key->numeric
                             + key->general_numeric
                             + key->human_numeric
                             + key->month
                             + (key->version | key->random | !!key->ignore);

      if (combined_key_score > 1)
      {
        char opts[sizeof short_options];

        /* Reset flags for compatibility check, preserving original side-effect. */
        key->skipsblanks = false;
        key->skipeblanks = false;
        key->reverse = false;

        key_to_opts (key, opts);
        incompatible_options (opts);
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
  int result;

  result = xstrtoumax (string, &suffix, 10, &n, "");

  if (result == LONGINT_INVALID)
    {
      if (msgid)
        error (SORT_FAILURE, 0, _("%s: invalid count at start of %s"),
               _(msgid), quote (string));
      return NULL;
    }
  else if ((result & LONGINT_OVERFLOW) || n > SIZE_MAX)
    {
      *val = SIZE_MAX;
    }
  else
    {
      *val = n;
    }
  
  return suffix;
}

/* Handle interrupts and hangups. */

static void
sighandler (int sig)
{
  cleanup ();

  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set the ordering options for KEY specified in S.
   Return the address of the first character in S that
   is not a valid ordering option.
   BLANKTYPE is the kind of blanks that 'b' should skip. */

static char *
set_ordering (char const *s, struct keyfield *key, enum blanktype blanktype)
{
  while (*s)
    {
      switch (*s)
        {
        case 'b':
          key->skipsblanks = (blanktype == bl_start || blanktype == bl_both);
          key->skipeblanks = (blanktype == bl_end || blanktype == bl_both);
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
          if (! key->ignore)
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
          return (char *) s;
        }
      ++s;
    }
  return (char *) s;
}

/* Initialize KEY.  */

static struct keyfield *
key_init (struct keyfield *key)
{
  if (key == NULL)
    {
      return NULL;
    }

  memset (key, 0, sizeof *key);
  key->eword = SIZE_MAX;
  return key;
}

#include <config.h>
#include <errno.h>
#include <getopt.h>
#include <locale.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#include "argmatch.h"
#include "array-cardinality.h"
#include "c-ctype.h"
#include "exit-failure.h"
#include "extent.h"
#include "fadvise.h"
#include "full-write.h"
#include "ignore-value.h"
#include "memchr.h"
#include "nproc.h"
#include "progname.h"
#include "quote.h"
#include "readtokens0.h"
#include "root-dev-ino.h"
#include "safe-read.h"
#include "size_overflow.h"
#include "stdio-safer.h"
#include "system.h"
#include "tempname.h"
#include "xalloc.h"
#include "xfopen.h"
#include "xstrtol.h"

#include "sort.h"
#include "sort.h" /* For SORT_FAILURE and EXIT_OUT_OF_ORDER */

/* Globals from sort.c */
extern char decimal_point;
extern char thousands_sep;
extern bool thousands_sep_ignored;
extern char eolchar;
extern char tab;
extern bool stable;
extern bool unique;
extern struct keyfield *keylist;
extern bool hard_LC_COLLATE;
extern bool hard_LC_TIME;
extern bool have_read_stdin;
extern char *compress_program;
extern bool debug;
extern char const *random_source;
extern size_t sort_size;
extern int reverse;
extern unsigned int temp_dir_count;
extern size_t default_nmerge; /* For NMERGE_OPTION */

/* Declarations for functions used in main */
extern void initialize_main (int *argc, char ***argv);
extern int posix2_version (void);
extern void inittables (void);
extern void key_init (struct keyfield *key);
extern char const *parse_field_count (char const *str, size_t *value, char const *msg);
extern char const *set_ordering (char const *str, struct keyfield *key, enum blank_behavior bl);
extern void badfieldspec (char const *optarg, char const *msg);
extern void insertkey (struct keyfield *key);
extern void incompatible_options (char const *s);
extern void specify_nmerge (int oi, int c, char *optarg);
extern void specify_sort_size (int oi, int c, char *optarg);
extern size_t specify_nthreads (int oi, int c, char *optarg);
extern void add_temp_dir (char *optarg);
extern bool default_key_compare (struct keyfield *key);
extern void check_ordering_compatibility (void);
extern void key_warnings (struct keyfield *gkey, bool gkey_only);
extern void random_md5_state_init (char const *random_source);
extern void check_inputs (char **files, size_t nfiles);
extern void check_output (char const *outfile);
extern void merge (struct sortfile *sortfiles, size_t from_file, size_t nfiles, char const *outfile);
extern void sort (char **files, size_t nfiles, char const *outfile, size_t nthreads);
extern bool check (char const *filename, char checkonly);
extern unsigned long int num_processors (int nproc_type);
extern void usage (int status);
extern void main_exit (int status);
extern void exit_cleanup (void);

/* Options */
enum
{
  CHECK_OPTION = 256,
  COMPRESS_PROGRAM_OPTION,
  DEBUG_PROGRAM_OPTION,
  FILES0_FROM_OPTION,
  NMERGE_OPTION,
  PARALLEL_OPTION,
  RANDOM_SOURCE_OPTION,
  SORT_OPTION,
  STABLE_OPTION, /* Not exposed as a separate option, but conceptually distinct */
  DEFAULT_MAX_THREADS = 8,
  MIN_SORT_SIZE = 128 * 1024
};

static char const *short_options = "bcCdDfghik:mMnorsS:t:T:uVy:z";
static struct option const long_options[] =
{
  {"batch-size", required_argument, nullptr, NMERGE_OPTION},
  {"buffer-size", required_argument, nullptr, 'S'},
  {"check", optional_argument, nullptr, CHECK_OPTION},
  {"compress-program", required_argument, nullptr, COMPRESS_PROGRAM_OPTION},
  {"debug", no_argument, nullptr, DEBUG_PROGRAM_OPTION},
  {"dictionary-order", no_argument, nullptr, 'd'},
  {"files0-from", required_argument, nullptr, FILES0_FROM_OPTION},
  {"field-separator", required_argument, nullptr, 't'},
  {"general-numeric-sort", no_argument, nullptr, 'g'},
  {"human-numeric-sort", no_argument, nullptr, 'h'},
  {"ignore-case", no_argument, nullptr, 'f'},
  {"ignore-leading-blanks", no_argument, nullptr, 'b'},
  {"ignore-nonprinting", no_argument, nullptr, 'i'},
  {"key", required_argument, nullptr, 'k'},
  {"merge", no_argument, nullptr, 'm'},
  {"month-sort", no_argument, nullptr, 'M'},
  {"numeric-sort", no_argument, nullptr, 'n'},
  {"output", required_argument, nullptr, 'o'},
  {"parallel", required_argument, nullptr, PARALLEL_OPTION},
  {"random-source", required_argument, nullptr, RANDOM_SOURCE_OPTION},
  {"reverse", no_argument, nullptr, 'r'},
  {"sort", required_argument, nullptr, SORT_OPTION},
  {"stable", no_argument, nullptr, STABLE_OPTION},
  {"temporary-directory", required_argument, nullptr, 'T'},
  {"threads", required_argument, nullptr, PARALLEL_OPTION},
  {"unique", no_argument, nullptr, 'u'},
  {"version-sort", no_argument, nullptr, 'V'},
  {"zero-terminated", no_argument, nullptr, 'z'},
  {GETOPT_HELP_OPTION_DECL},
  {GETOPT_VERSION_OPTION_DECL (PROGRAM_NAME, AUTHORS)},
  {nullptr, 0, nullptr, 0}
};

static char const *const sort_args[] =
{
  "general-numeric", "human-numeric", "month", "numeric", "random", "version", nullptr
};
static enum sort_type const sort_types[] =
{
  sort_general_numeric, sort_human_numeric, sort_month, sort_numeric, sort_random, sort_version
};

static char const *const check_args[] =
{
  "diagnose-first", "silent", nullptr
};
static enum check_type const check_types[] =
{
  'C', 'c'
};

/* Signal set for cleanup */
static sigset_t caught_signals;

/* Signal handler for cleanup */
static void
sighandler (int sig)
{
  /* If this process is the one that's killing this process group,
     then exit without a trace, so that another process can produce
     the diagnostic.  */
  if (getpgrp () == getpid ())
    _exit (128 + sig);

  /* Otherwise, exit and clean up as usual.  */
  exit (128 + sig);
}

static void setup_signals(void)
{
  size_t i;
  static int const sig[] =
  {
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
  enum { nsigs = ARRAY_CARDINALITY (sig) };

#if SA_NOCLDSTOP
  struct sigaction act;

  sigemptyset (&caught_signals);
  for (i = 0; i < nsigs; i++)
    {
      sigaction (sig[i], nullptr, &act);
      if (act.sa_handler != SIG_IGN)
        sigaddset (&caught_signals, sig[i]);
    }

  act.sa_handler = sighandler;
  act.sa_mask = caught_signals;
  act.sa_flags = 0;

  for (i = 0; i < nsigs; i++)
    if (sigismember (&caught_signals, sig[i]))
      sigaction (sig[i], &act, nullptr);
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

static void initialize_locale_info(void)
{
  struct lconv const *locale = localeconv ();

  decimal_point = locale->decimal_point[0];
  if (! decimal_point || locale->decimal_point[1])
    decimal_point = '.';

  thousands_sep = locale->thousands_sep[0];
  if (thousands_sep && locale->thousands_sep[1])
    thousands_sep_ignored = true;
  if (! thousands_sep || locale->thousands_sep[1])
    thousands_sep = NON_CHAR;
}

static void
handle_traditional_key_spec(char const *optarg, struct keyfield *key, bool *traditional_usage_ptr, bool posixly_correct)
{
  char const *s;
  bool minus_pos_usage = (optind != argc && argv[optind][0] == '-'
                          && c_isdigit (argv[optind][1]));
  *traditional_usage_ptr |= minus_pos_usage && !posixly_correct;

  if (*traditional_usage_ptr)
    {
      key_init (key);
      s = parse_field_count (optarg + 1, &key->sword, nullptr);
      if (s && *s == '.')
        s = parse_field_count (s + 1, &key->schar, nullptr);
      if (! (key->sword || key->schar))
        key->sword = SIZE_MAX;
      if (! s || *set_ordering (s, key, bl_start))
        {
          /* Not a valid key spec, treat as file. */
          key = nullptr;
        }
      else
        {
          if (minus_pos_usage)
            {
              char const *optarg1 = argv[optind++];
              s = parse_field_count (optarg1 + 1, &key->eword,
                                     N_("invalid number after '-'"));
              if (*s == '.')
                s = parse_field_count (s + 1, &key->echar,
                                       N_("invalid number after '.'"));
              if (!key->echar && key->eword)
                {
                  key->eword--;
                }
              if (*set_ordering (s, key, bl_end))
                badfieldspec (optarg1, N_("stray character in field spec"));
            }
          key->traditional_used = true;
          insertkey (key);
        }
    }
  else
    {
      key = nullptr; /* Treat as file */
    }
}

static void
parse_key_option(char const *optarg, struct keyfield *key)
{
  char const *s;

  key_init(key);

  s = parse_field_count(optarg, &key->sword, N_("invalid number at field start"));
  if (!key->sword--)
    badfieldspec(optarg, N_("field number is zero"));
  if (*s == '.')
    {
      s = parse_field_count(s + 1, &key->schar, N_("invalid number after '.'"));
      if (!key->schar--)
        badfieldspec(optarg, N_("character offset is zero"));
    }
  if (! (key->sword || key->schar))
    key->sword = SIZE_MAX;
  s = set_ordering(s, key, bl_start);
  if (*s != ',')
    {
      key->eword = SIZE_MAX;
      key->echar = 0;
    }
  else
    {
      s = parse_field_count(s + 1, &key->eword, N_("invalid number after ','"));
      if (!key->eword--)
        badfieldspec(optarg, N_("field number is zero"));
      if (*s == '.')
        s = parse_field_count(s + 1, &key->echar, N_("invalid number after '.'"));
      s = set_ordering(s, key, bl_end);
    }
  if (*s)
    badfieldspec(optarg, N_("stray character in field spec"));
  insertkey(key);
}

static void
handle_tab_option(char *optarg)
{
  char newtab = optarg[0];
  if (!newtab)
    error(SORT_FAILURE, 0, _("empty tab"));
  if (optarg[1])
    {
      if (STREQ(optarg, "\\0"))
        newtab = '\0';
      else
        error(SORT_FAILURE, 0, _("multi-character tab %s"), quote(optarg));
    }
  if (tab != TAB_DEFAULT && tab != newtab)
    error(SORT_FAILURE, 0, _("incompatible tabs"));
  tab = newtab;
}

static void
process_files0_from(char **files_ptr, size_t *nfiles_ptr, char const *files_from_name)
{
  if (*nfiles_ptr)
    {
      error (0, 0, _("extra operand %s"), quoteaf ((*files_ptr)[0]));
      fprintf (stderr, "%s\n",
               _("file operands cannot be combined with --files0-from"));
      usage (SORT_FAILURE);
    }

  FILE *stream = xfopen (files_from_name, "r");
  struct Tokens tok;
  readtokens0_init (&tok);

  if (!readtokens0 (stream, &tok))
    error (SORT_FAILURE, 0, _("cannot read file names from %s"), quoteaf (files_from_name));
  xfclose (stream, files_from_name);

  if (tok.n_tok)
    {
      free (*files_ptr);
      *files_ptr = tok.tok;
      *nfiles_ptr = tok.n_tok;
      for (size_t i = 0; i < *nfiles_ptr; i++)
        {
          if (STREQ ((*files_ptr)[i], "-"))
            error (SORT_FAILURE, 0, _("when reading file names from "
                                      "standard input, "
                                      "no file name of %s allowed"),
                   quoteaf ((*files_ptr)[i]));
          else if ((*files_ptr)[i][0] == '\0')
            {
              unsigned long int file_number = i + 1;
              error (SORT_FAILURE, 0,
                     _("%s:%lu: invalid zero-length file name"),
                     quotef (files_from_name), file_number);
            }
        }
    }
  else
    error (SORT_FAILURE, 0, _("no input from %s"), quoteaf (files_from_name));
}

int
main (int argc, char **argv)
{
  struct keyfield key_buf;
  struct keyfield gkey;
  bool gkey_only = false;
  char const *s;
  int c;
  char checkonly = 0;
  bool mergeonly = false;
  char *random_source = nullptr;
  bool need_random = false;
  size_t nthreads = 0;
  size_t nfiles = 0;
  bool posixly_correct = (getenv ("POSIXLY_CORRECT") != nullptr);
  int posix_ver = posix2_version ();
  bool traditional_usage = ! (200112 <= posix_ver && posix_ver < 200809);
  char **files;
  char *files_from = nullptr;
  char const *outfile = nullptr;
  bool locale_ok;

  initialize_main (&argc, &argv);
  set_program_name (argv[0]);
  locale_ok = !! setlocale (LC_ALL, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  initialize_exit_failure (SORT_FAILURE);

  hard_LC_COLLATE = hard_locale (LC_COLLATE);
#if HAVE_NL_LANGINFO
  hard_LC_TIME = hard_locale (LC_TIME);
#endif

  initialize_locale_info();
  have_read_stdin = false;
  inittables ();
  setup_signals();
  atexit (exit_cleanup);

  key_init (&gkey);
  gkey.sword = SIZE_MAX;

  files = xnmalloc (argc, sizeof *files);

  while (true)
    {
      int oi = -1;
      bool operand_is_file = false;

      if (c == -1 || ((c = getopt_long (argc, argv, short_options, long_options, &oi)) == -1))
        {
          if (argc <= optind)
            break;
          operand_is_file = true;
        }
      else if (posixly_correct && nfiles != 0 &&
               ! (traditional_usage && ! checkonly && optind != argc &&
                  argv[optind][0] == '-' && argv[optind][1] == 'o' &&
                  (argv[optind][2] || optind + 1 != argc)))
        {
          operand_is_file = true;
        }

      if (operand_is_file)
        {
          if (argc <= optind)
            break;
          files[nfiles++] = argv[optind++];
          continue;
        }

      switch (c)
        {
        case 1:
          {
            struct keyfield *current_key = &key_buf; /* Use stack for key_buf */
            handle_traditional_key_spec(optarg, current_key, &traditional_usage, posixly_correct);
            if (!current_key->traditional_used) /* If not treated as key, treat as file */
              files[nfiles++] = optarg;
          }
          break;

        case SORT_OPTION:
          c = XARGMATCH ("--sort", optarg, sort_args, sort_types);
          /* FALLTHROUGH */
        case 'b':
        case 'd':
        case 'f':
        case 'g':
        case 'h':
        case 'i':
        case 'M':
        case 'n':
        case 'r':
        case 'R':
        case 'V':
          {
            char str[2];
            str[0] = c;
            str[1] = '\0';
            set_ordering (str, &gkey, bl_both);
          }
          break;

        case CHECK_OPTION:
          c = (optarg
               ? XARGMATCH ("--check", optarg, check_args, check_types)
               : 'c');
          /* FALLTHROUGH */
        case 'c':
        case 'C':
          if (checkonly && checkonly != c)
            incompatible_options ("cC");
          checkonly = c;
          break;

        case COMPRESS_PROGRAM_OPTION:
          if (compress_program && !STREQ (compress_program, optarg))
            error (SORT_FAILURE, 0, _("multiple compress programs specified"));
          compress_program = optarg;
          break;

        case DEBUG_PROGRAM_OPTION:
          debug = true;
          break;

        case FILES0_FROM_OPTION:
          files_from = optarg;
          break;

        case 'k':
          parse_key_option(optarg, &key_buf);
          break;

        case 'm':
          mergeonly = true;
          break;

        case NMERGE_OPTION:
          specify_nmerge (oi, c, optarg);
          break;

        case 'o':
          if (outfile && !STREQ (outfile, optarg))
            error (SORT_FAILURE, 0, _("multiple output files specified"));
          outfile = optarg;
          break;

        case RANDOM_SOURCE_OPTION:
          if (random_source && !STREQ (random_source, optarg))
            error (SORT_FAILURE, 0, _("multiple random sources specified"));
          random_source = optarg;
          break;

        case STABLE_OPTION: /* Also -s, but handled implicitly */
        case 's':
          stable = true;
          break;

        case 'S':
          specify_sort_size (oi, c, optarg);
          break;

        case 't':
          handle_tab_option(optarg);
          break;

        case 'T':
          add_temp_dir (optarg);
          break;

        case PARALLEL_OPTION:
          nthreads = specify_nthreads (oi, c, optarg);
          break;

        case 'u':
          unique = true;
          break;

        case 'y':
          if (optarg == argv[optind - 1])
            {
              char const *p;
              for (p = optarg; c_isdigit (*p); p++)
                continue;
              optind -= (*p != '\0');
            }
          break;

        case 'z':
          eolchar = 0;
          break;

        case_GETOPT_HELP_CHAR;

        case_GETOPT_VERSION_CHAR (PROGRAM_NAME, AUTHORS);

        default:
          usage (SORT_FAILURE);
        }
    }

  if (files_from)
    process_files0_from(&files, &nfiles, files_from);

  for (struct keyfield *key = keylist; key; key = key->next)
    {
      if (default_key_compare (key) && !key->reverse)
        {
          key->ignore = gkey.ignore;
          key->translate = gkey.translate;
          key->skipsblanks = gkey.skipsblanks;
          key->skipeblanks = gkey.skipeblanks;
          key->month = gkey.month;
          key->numeric = gkey.numeric;
          key->general_numeric = gkey.general_numeric;
          key->human_numeric = gkey.human_numeric;
          key->version = gkey.version;
          key->random = gkey.random;
          key->reverse = gkey.reverse;
        }
      need_random |= key->random;
    }

  if (!keylist && !default_key_compare (&gkey))
    {
      gkey_only = true;
      insertkey (&gkey);
      need_random |= gkey.random;
    }

  check_ordering_compatibility ();

  if (debug)
    {
      if (checkonly || outfile)
        {
          static char opts[] = "X --debug";
          opts[0] = (checkonly ? checkonly : 'o');
          incompatible_options (opts);
        }

      if (locale_ok)
        locale_ok = !! setlocale (LC_COLLATE, "");
      if (!locale_ok)
        error (0, 0, "%s", _("failed to set locale"));
      if (hard_LC_COLLATE)
        error (0, 0, _("text ordering performed using %s sorting rules"),
               quote (setlocale (LC_COLLATE, nullptr)));
      else
        error (0, 0, "%s",
               _("text ordering performed using simple byte comparison"));

      key_warnings (&gkey, gkey_only);
    }

  reverse = gkey.reverse;

  if (need_random)
    random_md5_state_init (random_source);

  if (temp_dir_count == 0)
    {
      char const *tmp_dir = getenv ("TMPDIR");
      add_temp_dir ((char *)(tmp_dir ? tmp_dir : DEFAULT_TMPDIR)); /* Cast to char* is safe as add_temp_dir doesn't modify it */
    }

  if (nfiles == 0)
    {
      nfiles = 1;
      free (files);
      files = xmalloc (sizeof *files);
      *files = (char *) "-";
    }

  if (0 < sort_size)
    sort_size = MAX (sort_size, MIN_SORT_SIZE);

  if (checkonly)
    {
      if (nfiles > 1)
        error (SORT_FAILURE, 0, _("extra operand %s not allowed with -%c"),
               quoteaf (files[1]), checkonly);

      if (outfile)
        {
          static char opts[] = {0, 'o', 0};
          opts[0] = checkonly;
          incompatible_options (opts);
        }

      exit (check (files[0], checkonly) ? EXIT_SUCCESS : SORT_OUT_OF_ORDER);
    }

  check_inputs (files, nfiles);
  check_output (outfile);

  if (mergeonly)
    {
      struct sortfile *sortfiles = xcalloc (nfiles, sizeof *sortfiles);
      for (size_t i = 0; i < nfiles; ++i)
        sortfiles[i].name = files[i];
      merge (sortfiles, 0, nfiles, outfile);
      free(sortfiles);
    }
  else
    {
      if (!nthreads)
        {
          unsigned long int np = num_processors (NPROC_CURRENT_OVERRIDABLE);
          nthreads = MIN (np, DEFAULT_MAX_THREADS);
        }
      size_t nthreads_max = SIZE_MAX / (2 * sizeof (struct merge_node));
      nthreads = MIN (nthreads, nthreads_max);

      sort (files, nfiles, outfile, nthreads);
    }

  if (have_read_stdin && fclose (stdin) == EOF)
    sort_die (_("close failed"), "-");

  main_exit (EXIT_SUCCESS);
}
