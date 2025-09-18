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
  #define ERRNO_PREFIX ": errno "
  #define ERRNO_PREFIX_LEN 8
  #define NEWLINE "\n"
  #define NEWLINE_LEN 1

  ignore_value (write (STDERR_FILENO, errstr, strlen (errstr)));

  if (errnum)
    {
      char errbuf[INT_BUFSIZE_BOUND (errnum)];
      char *p = inttostr (errnum, errbuf);
      ignore_value (write (STDERR_FILENO, ERRNO_PREFIX, ERRNO_PREFIX_LEN));
      ignore_value (write (STDERR_FILENO, p, strlen (p)));
    }

  ignore_value (write (STDERR_FILENO, NEWLINE, NEWLINE_LEN));

  _exit (SORT_FAILURE);
}

/* Report MESSAGE for FILE, then clean up and exit.
   If FILE is null, it represents standard output.  */

static void
sort_die (char const *message, char const *file)
{
  char const *filename = file ? file : _("standard output");
  error (SORT_FAILURE, errno, "%s: %s", message, quotef (filename));
}

void print_usage_header(void)
{
    printf(_("\
Usage: %s [OPTION]... [FILE]...\n\
  or:  %s [OPTION]... --files0-from=F\n\
"), program_name, program_name);
    fputs(_("\
Write sorted concatenation of all FILE(s) to standard output.\n\
"), stdout);
    emit_stdin_note();
    emit_mandatory_arg_note();
}

void print_ordering_options(void)
{
    fputs(_("\
Ordering options:\n\
\n\
"), stdout);
    fputs(_("\
  -b, --ignore-leading-blanks  ignore leading blanks\n\
  -d, --dictionary-order      consider only blanks and alphanumeric characters\n\
  -f, --ignore-case           fold lower case to upper case characters\n\
"), stdout);
    fputs(_("\
  -g, --general-numeric-sort  compare according to general numerical value\n\
  -i, --ignore-nonprinting    consider only printable characters\n\
  -M, --month-sort            compare (unknown) < 'JAN' < ... < 'DEC'\n\
"), stdout);
    fputs(_("\
  -h, --human-numeric-sort    compare human readable numbers (e.g., 2K 1G)\n\
"), stdout);
    fputs(_("\
  -n, --numeric-sort          compare according to string numerical value;\n\
                                see full documentation for supported strings\n\
"), stdout);
    fputs(_("\
  -R, --random-sort           shuffle, but group identical keys.  See shuf(1)\n\
      --random-source=FILE    get random bytes from FILE\n\
  -r, --reverse               reverse the result of comparisons\n\
"), stdout);
    fputs(_("\
      --sort=WORD             sort according to WORD:\n\
                                general-numeric -g, human-numeric -h, month -M,\n\
                                numeric -n, random -R, version -V\n\
  -V, --version-sort          natural sort of (version) numbers within text\n\
\n\
"), stdout);
}

void print_other_options(void)
{
    fputs(_("\
Other options:\n\
\n\
"), stdout);
    fputs(_("\
      --batch-size=NMERGE   merge at most NMERGE inputs at once;\n\
                            for more use temp files\n\
"), stdout);
    fputs(_("\
  -c, --check, --check=diagnose-first  check for sorted input; do not sort\n\
  -C, --check=quiet, --check=silent  like -c, but do not report first bad line\n\
      --compress-program=PROG  compress temporaries with PROG;\n\
                              decompress them with PROG -d\n\
"), stdout);
    fputs(_("\
      --debug               annotate the part of the line used to sort, and\n\
                              warn about questionable usage to standard error\n\
      --files0-from=F       read input from the files specified by\n\
                            NUL-terminated names in file F;\n\
                            If F is - then read names from standard input\n\
"), stdout);
    fputs(_("\
  -k, --key=KEYDEF          sort via a key; KEYDEF gives location and type\n\
  -m, --merge               merge already sorted files; do not sort\n\
"), stdout);
    fputs(_("\
  -o, --output=FILE         write result to FILE instead of standard output\n\
  -s, --stable              stabilize sort by disabling last-resort comparison\n\
  -S, --buffer-size=SIZE    use SIZE for main memory buffer\n\
"), stdout);
    printf(_("\
  -t, --field-separator=SEP  use SEP instead of non-blank to blank transition\n\
  -T, --temporary-directory=DIR  use DIR for temporaries, not $TMPDIR or %s;\n\
                              multiple options specify multiple directories\n\
      --parallel=N          change the number of sorts run concurrently to N\n\
  -u, --unique              output only the first of lines with equal keys;\n\
                              with -c, check for strict ordering\n\
"), DEFAULT_TMPDIR);
    fputs(_("\
  -z, --zero-terminated     line delimiter is NUL, not newline\n\
"), stdout);
}

void print_help_and_version(void)
{
    fputs(HELP_OPTION_DESCRIPTION, stdout);
    fputs(VERSION_OPTION_DESCRIPTION, stdout);
}

void print_keydef_explanation(void)
{
    fputs(_("\
\n\
KEYDEF is F[.C][OPTS][,F[.C][OPTS]] for start and stop position, where F is a\n\
field number and C a character position in the field; both are origin 1, and\n\
the stop position defaults to the line's end.  If neither -t nor -b is in\n\
effect, characters in a field are counted from the beginning of the preceding\n\
whitespace.  OPTS is one or more single-letter ordering options [bdfgiMhnRrV],\n\
which override global ordering options for that key.  If no key is given, use\n\
the entire line as the key.  Use --debug to diagnose incorrect key usage.\n\
\n\
SIZE may be followed by the following multiplicative suffixes:\n\
"), stdout);
}

void print_size_suffixes_and_warning(void)
{
    fputs(_("\
% 1% of memory, b 1, K 1024 (default), and so on for M, G, T, P, E, Z, Y, R, Q.\n\n\
*** WARNING ***\n\
The locale specified by the environment affects sort order.\n\
Set LC_ALL=C to get the traditional sort order that uses\n\
native byte values.\n\
"), stdout);
}

void print_full_help(void)
{
    print_usage_header();
    print_ordering_options();
    print_other_options();
    print_help_and_version();
    print_keydef_explanation();
    print_size_suffixes_and_warning();
    emit_ancillary_info(PROGRAM_NAME);
}

void usage(int status)
{
    if (status != EXIT_SUCCESS)
        emit_try_help();
    else
        print_full_help();
    
    exit(status);
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
cs_enter(struct cs_status *status)
{
    const int SUCCESS = 0;
    int ret = pthread_sigmask(SIG_BLOCK, &caught_signals, &status->sigs);
    status->valid = (ret == SUCCESS);
}

/* Leave a critical section.  */
static void
cs_leave (struct cs_status const *status)
{
  if (!status->valid)
    return;
    
  pthread_sigmask (SIG_SETMASK, &status->sigs, nullptr);
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
  struct tempnode const *node = entry;
  return node->pid % tabsize;
}

static bool
proctab_comparator (void const *e1, void const *e2)
{
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
  pid_t cpid = waitpid ((pid ? pid : -1), &status, (pid ? 0 : WNOHANG));

  if (cpid < 0)
    {
      handle_wait_error();
    }
  else if (cpid > 0 && should_process_child(pid, cpid))
    {
      check_child_exit_status(status);
      --nprocs;
    }

  return cpid;
}

static void
handle_wait_error(void)
{
  error (SORT_FAILURE, errno, _("waiting for %s [-d]"),
         quoteaf (compress_program));
}

static int
should_process_child(pid_t pid, pid_t cpid)
{
  return (pid > 0 || delete_proc (cpid));
}

static void
check_child_exit_status(int status)
{
  if (! WIFEXITED (status) || WEXITSTATUS (status))
    error (SORT_FAILURE, 0, _("%s [-d] terminated abnormally"),
           quoteaf (compress_program));
}

/* TEMP represents a new process; add it to the process table.  Create
   the process table the first time it's called.  */

static void initialize_proctab_if_needed(void)
{
    if (proctab)
        return;
    
    proctab = hash_initialize(INIT_PROCTAB_SIZE, nullptr,
                              proctab_hasher,
                              proctab_comparator,
                              nullptr);
    if (!proctab)
        xalloc_die();
}

static void insert_temp_into_proctab(struct tempnode *temp)
{
    if (!hash_insert(proctab, temp))
        xalloc_die();
}

static void register_proc(struct tempnode *temp)
{
    initialize_proctab_if_needed();
    temp->state = UNREAPED;
    insert_temp_into_proctab(temp);
}

/* If PID is in the process table, remove it and return true.
   Otherwise, return false.  */

static bool
delete_proc (pid_t pid)
{
  struct tempnode test;

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
  if (delete_proc (pid))
    reap (pid);
}

/* Reap any exited children.  Do not block; reap only those that have
   already exited.  */

static void reap_exited(void)
{
    while (nprocs > 0 && reap(0))
        ;
}

/* Reap at least one exited child, waiting if necessary.  */

static void reap_some(void)
{
    reap(-1);
    reap_exited();
}

/* Reap all children, waiting if necessary.  */

static void reap_all(void)
{
    while (nprocs > 0)
    {
        reap(-1);
    }
}

/* Clean up any remaining temporary files.  */

static void
cleanup (void)
{
  struct tempnode const *node = temphead;
  
  while (node)
    {
      unlink (node->name);
      node = node->next;
    }
    
  temphead = nullptr;
}

/* Cleanup actions to take when exiting.  */

static void
exit_cleanup (void)
{
  if (temphead)
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

static struct tempnode *allocate_temp_node(const char *temp_dir)
{
  static char const slashbase[] = "/sortXXXXXX";
  size_t len = strlen(temp_dir);
  struct tempnode *node = 
    xmalloc(FLEXSIZEOF(struct tempnode, name, len + sizeof slashbase));
  char *file = node->name;
  
  memcpy(file, temp_dir, len);
  memcpy(file + len, slashbase, sizeof slashbase);
  node->next = nullptr;
  
  return node;
}

static const char *get_next_temp_dir(void)
{
  static idx_t temp_dir_index;
  const char *temp_dir = temp_dirs[temp_dir_index];
  
  if (++temp_dir_index == temp_dir_count)
    temp_dir_index = 0;
    
  return temp_dir;
}

static int create_temp_fd_with_cs(struct tempnode *node)
{
  struct cs_status cs;
  int fd;
  int saved_errno;
  
  cs_enter(&cs);
  fd = mkostemp(node->name, O_CLOEXEC);
  if (0 <= fd)
    {
      *temptail = node;
      temptail = &node->next;
    }
  saved_errno = errno;
  cs_leave(&cs);
  errno = saved_errno;
  
  return fd;
}

static void handle_temp_creation_error(struct tempnode *node, 
                                      const char *temp_dir,
                                      bool survive_fd_exhaustion)
{
  if (!(survive_fd_exhaustion && errno == EMFILE))
    error(SORT_FAILURE, errno, _("cannot create temporary file in %s"),
          quoteaf(temp_dir));
  free(node);
}

static struct tempnode *
create_temp_file(int *pfd, bool survive_fd_exhaustion)
{
  const char *temp_dir = get_next_temp_dir();
  struct tempnode *node = allocate_temp_node(temp_dir);
  
  int fd = create_temp_fd_with_cs(node);
  
  if (fd < 0)
    {
      handle_temp_creation_error(node, temp_dir, survive_fd_exhaustion);
      node = nullptr;
    }
    
  *pfd = fd;
  return node;
}

/* Return a pointer to stdout status, or nullptr on failure.  */

static struct stat *
get_outstatus (void)
{
  static int outstat_errno;
  static struct stat outstat;
  
  if (outstat_errno == 0)
  {
    int fstat_result = fstat (STDOUT_FILENO, &outstat);
    outstat_errno = (fstat_result == 0) ? -1 : errno;
  }
  
  return (outstat_errno < 0) ? &outstat : nullptr;
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

static FILE *open_read_stream(char const *file)
{
    if (STREQ(file, "-"))
    {
        have_read_stdin = true;
        return stdin;
    }
    
    int fd = open(file, O_RDONLY | O_CLOEXEC);
    return fd < 0 ? nullptr : fdopen(fd, "r");
}

static void truncate_output_file(char const *file)
{
    if (!file || ftruncate(STDOUT_FILENO, 0) == 0)
        return;
    
    int ftruncate_errno = errno;
    struct stat *outst = get_outstatus();
    
    if (!outst || S_ISREG(outst->st_mode) || S_TYPEISSHM(outst))
        error(SORT_FAILURE, ftruncate_errno, _("%s: error truncating"), quotef(file));
}

static FILE *stream_open(char const *file, char const *how)
{
    FILE *fp;
    
    if (*how == 'r')
    {
        fp = open_read_stream(file);
        fadvise(fp, FADVISE_SEQUENTIAL);
    }
    else if (*how == 'w')
    {
        truncate_output_file(file);
        fp = stdout;
    }
    else
    {
        affirm(!"unexpected mode passed to stream_open");
    }
    
    return fp;
}

/* Same as stream_open, except always return a non-null value; die on
   failure.  */

static FILE *
xfopen(char const *file, char const *how)
{
    FILE *fp = stream_open(file, how);
    if (!fp)
        sort_die(_("open failed"), file);
    return fp;
}

/* Close FP, whose name is FILE, and report any errors.  */

static void flush_stdout(FILE *fp, char const *file)
{
    if (fflush(fp) != 0)
        sort_die(_("fflush failed"), file);
}

static void close_file(FILE *fp, char const *file)
{
    if (fclose(fp) != 0)
        sort_die(_("close failed"), file);
}

static void xfclose(FILE *fp, char const *file)
{
    int fd = fileno(fp);
    
    if (fd == STDIN_FILENO)
    {
        clearerr(fp);
    }
    else if (fd == STDOUT_FILENO)
    {
        flush_stdout(fp, file);
    }
    else
    {
        close_file(fp, file);
    }
}

/* Move OLDFD to NEWFD.  If OLDFD != NEWFD, NEWFD is not close-on-exec.  */

static void
move_fd (int oldfd, int newfd)
{
  if (oldfd == newfd)
    return;
    
  ignore_value (dup2 (oldfd, newfd));
  ignore_value (close (oldfd));
}

/* Fork a child process for piping to and do common cleanup.  The
   TRIES parameter specifies how many times to try to fork before
   giving up.  Return the PID of the child, or -1 (setting errno)
   on failure. */

static pid_t
pipe_fork (int pipefds[2], size_t tries)
{
#if HAVE_WORKING_FORK
  #define INITIAL_WAIT_RETRY 0.25
  #define WAIT_RETRY_MULTIPLIER 2
  #define MIN_SUBPROCESSES_NEEDED 1

  struct tempnode *saved_temphead;
  int saved_errno;
  double wait_retry = INITIAL_WAIT_RETRY;
  pid_t pid;
  struct cs_status cs;

  if (pipe2 (pipefds, O_CLOEXEC) < 0)
    return -1;

  if (nmerge + MIN_SUBPROCESSES_NEEDED < nprocs)
    reap_some ();

  pid = attempt_fork_with_retry(&wait_retry, tries, &saved_temphead, &cs);

  if (pid < 0)
    handle_fork_failure(pipefds);
  else if (pid == 0)
    handle_child_process();
  else
    handle_parent_process();

  return pid;
#else
  return -1;
#endif
}

#if HAVE_WORKING_FORK
static pid_t
attempt_fork_with_retry(double *wait_retry, size_t tries, 
                       struct tempnode **saved_temphead, struct cs_status *cs)
{
  pid_t pid;
  int saved_errno;

  while (tries--)
    {
      pid = perform_fork(saved_temphead, cs, &saved_errno);
      
      if (0 <= pid || errno != EAGAIN)
        break;
      
      wait_and_retry(wait_retry);
    }
  
  return pid;
}

static pid_t
perform_fork(struct tempnode **saved_temphead, struct cs_status *cs, int *saved_errno)
{
  pid_t pid;
  
  cs_enter (cs);
  *saved_temphead = temphead;
  temphead = nullptr;

  pid = fork ();
  *saved_errno = errno;
  
  if (pid)
    temphead = *saved_temphead;

  cs_leave (cs);
  errno = *saved_errno;
  
  return pid;
}

static void
wait_and_retry(double *wait_retry)
{
  xnanosleep (*wait_retry);
  *wait_retry *= WAIT_RETRY_MULTIPLIER;
  reap_exited ();
}

static void
handle_fork_failure(int pipefds[2])
{
  int saved_errno = errno;
  close (pipefds[0]);
  close (pipefds[1]);
  errno = saved_errno;
}

static void
handle_child_process(void)
{
  close (STDIN_FILENO);
  close (STDOUT_FILENO);
}

static void
handle_parent_process(void)
{
  ++nprocs;
}
#endif

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
  if (! node)
    return nullptr;

  node->state = UNCOMPRESSED;

  if (compress_program)
    tempfd = setup_compression(node, tempfd);

  *pfp = fdopen (tempfd, "w");
  if (! *pfp)
    sort_die (_("couldn't create temporary file"), node->name);

  return node;
}

static int setup_compression(struct tempnode *node, int tempfd)
{
  int pipefds[2];
  node->pid = pipe_fork (pipefds, MAX_FORK_TRIES_COMPRESS);
  
  if (node->pid > 0)
    return handle_parent_process(node, tempfd, pipefds);
  
  if (node->pid == 0)
    handle_child_process(tempfd, pipefds);
  
  return tempfd;
}

static int handle_parent_process(struct tempnode *node, int tempfd, int pipefds[2])
{
  close (tempfd);
  close (pipefds[0]);
  register_proc (node);
  return pipefds[1];
}

static void handle_child_process(int tempfd, int pipefds[2])
{
  close (pipefds[1]);
  move_fd (tempfd, STDOUT_FILENO);
  move_fd (pipefds[0], STDIN_FILENO);
  execlp (compress_program, compress_program, (char *) nullptr);
  async_safe_die (errno, "couldn't execute compress program");
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return the address
   of the new temp node.  Die on failure.  */

static struct tempnode *
create_temp (FILE **pfp)
{
  return maybe_create_temp (pfp, false);
}

/* Open a compressed temp file and start a decompression process through
   which to filter the input.  Return nullptr (setting errno to
   EMFILE) if we ran out of file descriptors, and die on any other
   kind of failure.  */

static FILE *
open_temp (struct tempnode *temp)
{
  int tempfd, pipefds[2];
  FILE *fp = nullptr;

  if (temp->state == UNREAPED)
    wait_proc (temp->pid);

  tempfd = open (temp->name, O_RDONLY);
  if (tempfd < 0)
    return nullptr;

  pid_t child = pipe_fork (pipefds, MAX_FORK_TRIES_DECOMPRESS);

  if (child == -1)
    return handle_fork_error (tempfd);
  
  if (child == 0)
    setup_child_process (tempfd, pipefds);
  
  return setup_parent_process (temp, child, tempfd, pipefds);
}

static FILE *
handle_fork_error (int tempfd)
{
  if (errno != EMFILE)
    error (SORT_FAILURE, errno, _("couldn't create process for %s -d"),
           quoteaf (compress_program));
  close (tempfd);
  errno = EMFILE;
  return nullptr;
}

static void
setup_child_process (int tempfd, int pipefds[2])
{
  close (pipefds[0]);
  move_fd (tempfd, STDIN_FILENO);
  move_fd (pipefds[1], STDOUT_FILENO);

  execlp (compress_program, compress_program, "-d", (char *) nullptr);

  async_safe_die (errno, "couldn't execute compress program (with -d)");
}

static FILE *
setup_parent_process (struct tempnode *temp, pid_t child, int tempfd, int pipefds[2])
{
  temp->pid = child;
  register_proc (temp);
  close (tempfd);
  close (pipefds[1]);

  FILE *fp = fdopen (pipefds[0], "r");
  if (!fp)
    {
      int saved_errno = errno;
      close (pipefds[0]);
      errno = saved_errno;
    }
  return fp;
}

/* Append DIR to the array of temporary directory names.  */
static void
add_temp_dir (char const *dir)
{
  if (temp_dir_count == temp_dir_alloc)
    temp_dirs = xpalloc (temp_dirs, &temp_dir_alloc, 1, -1, sizeof *temp_dirs);

  temp_dirs[temp_dir_count++] = dir;
}

/* Remove NAME from the list of temporary files.  */

static struct tempnode* find_temp_node(char const *name, struct tempnode *volatile **pnode)
{
    struct tempnode *node;
    for (*pnode = &temphead; (node = **pnode)->name != name; *pnode = &node->next)
        continue;
    return node;
}

static void wait_for_unreaped_process(struct tempnode *node)
{
    if (node->state == UNREAPED)
        wait_proc(node->pid);
}

static int unlink_temp_file(char const *name, struct tempnode *next, 
                           struct tempnode *volatile **pnode, int *unlink_errno)
{
    struct cs_status cs;
    int unlink_status;
    
    cs_enter(&cs);
    unlink_status = unlink(name);
    *unlink_errno = errno;
    **pnode = next;
    cs_leave(&cs);
    
    return unlink_status;
}

static void handle_unlink_error(int unlink_status, int unlink_errno, char const *name)
{
    if (unlink_status != 0)
        error(0, unlink_errno, _("warning: cannot remove: %s"), quotef(name));
}

static void update_temptail_if_needed(struct tempnode *next, struct tempnode *volatile **pnode)
{
    if (!next)
        temptail = pnode;
}

static void zaptemp(char const *name)
{
    struct tempnode *volatile *pnode;
    struct tempnode *node;
    struct tempnode *next;
    int unlink_status;
    int unlink_errno = 0;

    node = find_temp_node(name, &pnode);
    wait_for_unreaped_process(node);
    
    next = node->next;
    unlink_status = unlink_temp_file(name, next, &pnode, &unlink_errno);
    
    handle_unlink_error(unlink_status, unlink_errno, name);
    update_temptail_if_needed(next, &pnode);
    free(node);
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

static void init_character_tables(void)
{
  size_t i;
  for (i = 0; i < UCHAR_LIM; ++i)
    {
      blanks[i] = i == '\n' || isblank(i);
      nondictionary[i] = !blanks[i] && !isalnum(i);
      nonprinting[i] = !isprint(i);
      fold_toupper[i] = toupper(i);
    }
}

#if HAVE_NL_LANGINFO
static char* extract_month_name(const char *s, size_t s_len)
{
  size_t j, k;
  char *name = xmalloc(s_len + 1);
  
  for (j = k = 0; j < s_len; j++)
    {
      if (!isblank(to_uchar(s[j])))
        name[k++] = fold_toupper[to_uchar(s[j])];
    }
  name[k] = '\0';
  
  return name;
}

static void init_month_table(void)
{
  size_t i;
  for (i = 0; i < MONTHS_PER_YEAR; i++)
    {
      const char *s = nl_langinfo(ABMON_1 + i);
      size_t s_len = strlen(s);
      
      monthtab[i].name = extract_month_name(s, s_len);
      monthtab[i].val = i + 1;
    }
  qsort(monthtab, MONTHS_PER_YEAR, sizeof *monthtab, struct_month_cmp);
}
#endif

static void inittables(void)
{
  init_character_tables();
  
#if HAVE_NL_LANGINFO
  if (hard_LC_TIME)
    init_month_table();
#endif
}

/* Specify how many inputs may be merged at once.
   This may be set on the command-line with the
   --batch-size option. */
static unsigned int get_max_nmerge(void)
{
    struct rlimit rlimit;
    unsigned int max_open_files = (getrlimit(RLIMIT_NOFILE, &rlimit) == 0) 
                                   ? rlimit.rlim_cur 
                                   : OPEN_MAX;
    const unsigned int RESERVED_FDS = 3;
    return max_open_files - RESERVED_FDS;
}

static void handle_nmerge_too_small(int oi, char const *s)
{
    const char *MIN_NMERGE = "2";
    error(0, 0, _("invalid --%s argument %s"),
          long_options[oi].name, quote(s));
    error(SORT_FAILURE, 0,
          _("minimum --%s argument is %s"),
          long_options[oi].name, quote(MIN_NMERGE));
}

static void handle_nmerge_overflow(int oi, char const *s, unsigned int max_nmerge)
{
    error(0, 0, _("--%s argument %s too large"),
          long_options[oi].name, quote(s));
    error(SORT_FAILURE, 0,
          _("maximum --%s argument with current rlimit is %u"),
          long_options[oi].name, max_nmerge);
}

static void validate_nmerge_range(int oi, char const *s, uintmax_t n, unsigned int max_nmerge)
{
    const uintmax_t MIN_NMERGE = 2;
    
    if (n < MIN_NMERGE)
    {
        handle_nmerge_too_small(oi, s);
    }
    else if (max_nmerge < n)
    {
        handle_nmerge_overflow(oi, s, max_nmerge);
    }
}

static void specify_nmerge(int oi, char c, char const *s)
{
    uintmax_t n;
    enum strtol_error e = xstrtoumax(s, nullptr, 10, &n, "");
    unsigned int max_nmerge = get_max_nmerge();

    if (e != LONGINT_OK)
    {
        xstrtol_fatal(e, oi, c, long_options, s);
        return;
    }

    nmerge = n;
    if (nmerge != n)
    {
        handle_nmerge_overflow(oi, s, max_nmerge);
        return;
    }

    if (nmerge >= 2 && nmerge <= max_nmerge)
    {
        return;
    }

    validate_nmerge_range(oi, s, nmerge, max_nmerge);
}

/* Specify the amount of main memory to use when sorting.  */
static void
convert_to_bytes(uintmax_t *n, enum strtol_error *e)
{
  if (*n <= UINTMAX_MAX / 1024)
    *n *= 1024;
  else
    *e = LONGINT_OVERFLOW;
}

static void
handle_byte_suffix(enum strtol_error *e)
{
  *e = LONGINT_OK;
}

static void
handle_percent_suffix(uintmax_t *n, enum strtol_error *e)
{
  double mem = physmem_total() * (*n) / 100;
  
  if (mem < UINTMAX_MAX)
  {
    *n = mem;
    *e = LONGINT_OK;
  }
  else
  {
    *e = LONGINT_OVERFLOW;
  }
}

static void
process_suffix(char const *suffix, uintmax_t *n, enum strtol_error *e)
{
  if (*e != LONGINT_INVALID_SUFFIX_CHAR || !c_isdigit(suffix[-1]) || suffix[1])
    return;
    
  switch (suffix[0])
  {
    case 'b':
      handle_byte_suffix(e);
      break;
    case '%':
      handle_percent_suffix(n, e);
      break;
  }
}

static void
update_sort_size(uintmax_t n)
{
  if (n < sort_size)
    return;
    
  sort_size = n;
  if (sort_size == n)
    sort_size = MAX(sort_size, MIN_SORT_SIZE);
}

static void
specify_sort_size(int oi, char c, char const *s)
{
  uintmax_t n;
  char *suffix;
  enum strtol_error e = xstrtoumax(s, &suffix, 10, &n, "EgGkKmMPQRtTYZ");
  
  if (e == LONGINT_OK && c_isdigit(suffix[-1]))
    convert_to_bytes(&n, &e);
    
  process_suffix(suffix, &n, &e);
  
  if (e == LONGINT_OK)
  {
    update_sort_size(n);
    if (sort_size == n)
      return;
    e = LONGINT_OVERFLOW;
  }
  
  xstrtol_fatal(e, oi, c, long_options, s);
}

/* Specify the number of threads to spawn during internal sort.  */
static size_t
specify_nthreads (int oi, char c, char const *s)
{
  uintmax_t nthreads;
  enum strtol_error e = xstrtoumax (s, nullptr, 10, &nthreads, "");
  
  if (e == LONGINT_OVERFLOW)
    return SIZE_MAX;
    
  if (e != LONGINT_OK)
    xstrtol_fatal (e, oi, c, long_options, s);
    
  if (SIZE_MAX < nthreads)
    nthreads = SIZE_MAX;
    
  if (nthreads == 0)
    error (SORT_FAILURE, 0, _("number in parallel must be nonzero"));
    
  return nthreads;
}

/* Return the default sort size.  */
static size_t get_resource_limit(int resource_type, size_t current_size)
{
    struct rlimit rlimit;
    if (getrlimit(resource_type, &rlimit) == 0 && rlimit.rlim_cur < current_size)
        return rlimit.rlim_cur;
    return current_size;
}

static size_t apply_data_and_as_limits(size_t size)
{
    size = get_resource_limit(RLIMIT_DATA, size);
#ifdef RLIMIT_AS
    size = get_resource_limit(RLIMIT_AS, size);
#endif
    return size / 2;
}

static size_t apply_rss_limit(size_t size)
{
#ifdef RLIMIT_RSS
    struct rlimit rlimit;
    const size_t RSS_MARGIN_NUMERATOR = 15;
    const size_t RSS_MARGIN_DENOMINATOR = 16;
    
    if (getrlimit(RLIMIT_RSS, &rlimit) == 0) {
        size_t rss_limit = rlimit.rlim_cur / RSS_MARGIN_DENOMINATOR * RSS_MARGIN_NUMERATOR;
        if (rss_limit < size)
            return rss_limit;
    }
#endif
    return size;
}

static size_t apply_physical_memory_limit(size_t size)
{
    const double PHYSICAL_MEMORY_MARGIN = 0.75;
    const double TOTAL_MEMORY_DIVISOR = 8.0;
    
    double avail = physmem_available();
    double total = physmem_total();
    double mem = MAX(avail, total / TOTAL_MEMORY_DIVISOR);
    
    if (total * PHYSICAL_MEMORY_MARGIN < size)
        size = total * PHYSICAL_MEMORY_MARGIN;
    
    if (mem < size)
        size = mem;
    
    return size;
}

static size_t default_sort_size(void)
{
    size_t size = SIZE_MAX;
    
    size = apply_data_and_as_limits(size);
    size = apply_rss_limit(size);
    size = apply_physical_memory_limit(size);
    
    return MAX(size, MIN_SORT_SIZE);
}

/* Return the sort buffer size to use with the input files identified
   by FPS and FILES, which are alternate names of the same files.
   NFILES gives the number of input files; NFPS may be less.  Assume
   that each input line requires LINE_BYTES extra bytes' worth of line
   information.  Do not exceed the size bound specified by the user
   (or a default size bound, if the user does not specify one).  */

static int get_file_stat(FILE *const *fps, size_t nfps, char *const *files, size_t i, struct stat *st)
{
    if (i < nfps)
        return fstat(fileno(fps[i]), st);
    
    if (STREQ(files[i], "-"))
        return fstat(STDIN_FILENO, st);
    
    return stat(files[i], st);
}

static off_t get_file_size(struct stat *st)
{
    if (usable_st_size(st) && 0 < st->st_size)
        return st->st_size;
    
    if (sort_size)
        return -1;
    
    return INPUT_FILE_SIZE_GUESS;
}

static void initialize_size_bound(void)
{
    if (size_bound)
        return;
    
    size_bound = sort_size;
    if (!size_bound)
        size_bound = default_sort_size();
}

static int check_overflow(off_t file_size, size_t worst_case_per_input_byte, size_t worst_case)
{
    return file_size != worst_case / worst_case_per_input_byte;
}

static int exceeds_bound(size_t size, size_t worst_case)
{
    return size_bound - size <= worst_case;
}

static size_t
sort_buffer_size (FILE *const *fps, size_t nfps,
                  char *const *files, size_t nfiles,
                  size_t line_bytes)
{
    static size_t size_bound;
    
    size_t worst_case_per_input_byte = line_bytes + 1;
    size_t size = worst_case_per_input_byte + 1;
    
    for (size_t i = 0; i < nfiles; i++)
    {
        struct stat st;
        
        if (get_file_stat(fps, nfps, files, i, &st) != 0)
            sort_die(_("stat failed"), files[i]);
        
        off_t file_size = get_file_size(&st);
        if (file_size == -1)
            return sort_size;
        
        initialize_size_bound();
        
        size_t worst_case = file_size * worst_case_per_input_byte + 1;
        
        if (check_overflow(file_size, worst_case_per_input_byte, worst_case) || 
            exceeds_bound(size, worst_case))
            return size_bound;
        
        size += worst_case;
    }
    
    return size;
}

/* Initialize BUF.  Reserve LINE_BYTES bytes for each line; LINE_BYTES
   must be at least sizeof (struct line).  Allocate ALLOC bytes
   initially.  */

static size_t align_to_line_struct(size_t alloc)
{
    return alloc + sizeof(struct line) - alloc % sizeof(struct line);
}

static void *allocate_buffer(size_t *alloc, size_t line_bytes)
{
    void *buffer = NULL;
    
    while (buffer == NULL)
    {
        *alloc = align_to_line_struct(*alloc);
        buffer = malloc(*alloc);
        
        if (buffer == NULL)
        {
            *alloc /= 2;
            if (*alloc <= line_bytes + 1)
                xalloc_die();
        }
    }
    
    return buffer;
}

static void reset_buffer_state(struct buffer *buf)
{
    buf->used = 0;
    buf->left = 0;
    buf->nlines = 0;
    buf->eof = false;
}

static void initbuf(struct buffer *buf, size_t line_bytes, size_t alloc)
{
    buf->buf = allocate_buffer(&alloc, line_bytes);
    buf->line_bytes = line_bytes;
    buf->alloc = alloc;
    reset_buffer_state(buf);
}

/* Return one past the limit of the line array.  */

static inline struct line *
buffer_linelim (struct buffer const *buf)
{
  void *linelim = buf->buf + buf->alloc;
  return linelim;
}

/* Return a pointer to the first character of the field specified
   by KEY in LINE. */

static char *skip_to_tab(char *ptr, char *lim)
{
    while (ptr < lim && *ptr != tab)
        ++ptr;
    if (ptr < lim)
        ++ptr;
    return ptr;
}

static char *skip_blanks(char *ptr, char *lim)
{
    while (ptr < lim && blanks[to_uchar(*ptr)])
        ++ptr;
    return ptr;
}

static char *skip_non_blanks(char *ptr, char *lim)
{
    while (ptr < lim && !blanks[to_uchar(*ptr)])
        ++ptr;
    return ptr;
}

static char *skip_default_field(char *ptr, char *lim)
{
    ptr = skip_blanks(ptr, lim);
    ptr = skip_non_blanks(ptr, lim);
    return ptr;
}

static char *skip_fields_with_tab(char *ptr, char *lim, size_t count)
{
    while (ptr < lim && count--)
        ptr = skip_to_tab(ptr, lim);
    return ptr;
}

static char *skip_fields_default(char *ptr, char *lim, size_t count)
{
    while (ptr < lim && count--)
        ptr = skip_default_field(ptr, lim);
    return ptr;
}

static char *advance_by_chars(char *ptr, char *lim, size_t schar)
{
    size_t remaining_bytes = lim - ptr;
    if (schar < remaining_bytes)
        return ptr + schar;
    return lim;
}

static char *
begfield (struct line const *line, struct keyfield const *key)
{
    char *ptr = line->text, *lim = ptr + line->length - 1;
    size_t sword = key->sword;
    size_t schar = key->schar;

    if (tab != TAB_DEFAULT)
        ptr = skip_fields_with_tab(ptr, lim, sword);
    else
        ptr = skip_fields_default(ptr, lim, sword);

    if (key->skipsblanks)
        ptr = skip_blanks(ptr, lim);

    ptr = advance_by_chars(ptr, lim, schar);

    return ptr;
}

/* Return the limit of (a pointer to the first character after) the field
   in LINE specified by KEY. */

ATTRIBUTE_PURE
static char *
limfield (struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text, *lim = ptr + line->length - 1;
  size_t eword = key->eword, echar = key->echar;

  if (echar == 0)
    eword++;

  ptr = skip_fields(ptr, lim, eword, echar);

#ifdef POSIX_UNSPECIFIED
  lim = adjust_field_limit(ptr, lim);
#endif

  if (echar != 0)
    ptr = skip_end_characters(ptr, lim, echar, key->skipeblanks);

  return ptr;
}

static char *
skip_fields(char *ptr, char *lim, size_t eword, size_t echar)
{
  if (tab != TAB_DEFAULT)
    return skip_fields_with_tab(ptr, lim, eword, echar);
  else
    return skip_fields_with_blanks(ptr, lim, eword);
}

static char *
skip_fields_with_tab(char *ptr, char *lim, size_t eword, size_t echar)
{
  while (ptr < lim && eword--)
    {
      ptr = skip_until_tab(ptr, lim);
      if (ptr < lim && (eword || echar))
        ++ptr;
    }
  return ptr;
}

static char *
skip_until_tab(char *ptr, char *lim)
{
  while (ptr < lim && *ptr != tab)
    ++ptr;
  return ptr;
}

static char *
skip_fields_with_blanks(char *ptr, char *lim, size_t eword)
{
  while (ptr < lim && eword--)
    {
      ptr = skip_blanks(ptr, lim);
      ptr = skip_non_blanks(ptr, lim);
    }
  return ptr;
}

static char *
skip_blanks(char *ptr, char *lim)
{
  while (ptr < lim && blanks[to_uchar (*ptr)])
    ++ptr;
  return ptr;
}

static char *
skip_non_blanks(char *ptr, char *lim)
{
  while (ptr < lim && !blanks[to_uchar (*ptr)])
    ++ptr;
  return ptr;
}

#ifdef POSIX_UNSPECIFIED
static char *
adjust_field_limit(char *ptr, char *lim)
{
  if (tab != TAB_DEFAULT)
    {
      char *newlim = memchr (ptr, tab, lim - ptr);
      if (newlim)
        return newlim;
    }
  else
    {
      char *newlim = ptr;
      newlim = skip_blanks(newlim, lim);
      newlim = skip_non_blanks(newlim, lim);
      return newlim;
    }
  return lim;
}
#endif

static char *
skip_end_characters(char *ptr, char *lim, size_t echar, bool skipeblanks)
{
  if (skipeblanks)
    ptr = skip_blanks(ptr, lim);

  size_t remaining_bytes = lim - ptr;
  if (echar < remaining_bytes)
    return ptr + echar;
  else
    return lim;
}

/* Fill BUF reading from FP, moving buf->left bytes from the end
   of buf->buf to the beginning first.  If EOF is reached and the
   file wasn't terminated by a newline, supply one.  Set up BUF's line
   table too.  FILE is the name of the file corresponding to FP.
   Return true if some input was read.  */

static bool check_eof_conditions(struct buffer *buf, FILE *fp, char const *file, char *ptrlim, char *line_start, char eol)
{
    if (ferror(fp))
        sort_die(_("read failed"), file);
    if (feof(fp))
    {
        buf->eof = true;
        if (buf->buf == ptrlim)
            return true;
        if (line_start != ptrlim && ptrlim[-1] != eol)
            *ptrlim++ = eol;
    }
    return false;
}

static void setup_key_limits(struct line *line, struct keyfield const *key, char *p, char *line_start)
{
    line->keylim = (key->eword == SIZE_MAX ? p : limfield(line, key));
    
    if (key->sword != SIZE_MAX)
    {
        line->keybeg = begfield(line, key);
    }
    else
    {
        if (key->skipsblanks)
            while (blanks[to_uchar(*line_start)])
                line_start++;
        line->keybeg = line_start;
    }
}

static void process_line(struct line *line, char *line_start, char *ptr, size_t *mergesize, struct keyfield const *key, char *p)
{
    *p = '\0';
    line->text = line_start;
    line->length = (p + 1) - line_start;
    *mergesize = MAX(*mergesize, line->length);
    
    if (key)
        setup_key_limits(line, key, p, line_start);
}

static size_t read_input_chunk(FILE *fp, char *ptr, size_t avail, size_t line_bytes)
{
    size_t readsize = (avail - 1) / (line_bytes + 1);
    return fread(ptr, 1, readsize, fp);
}

static char* find_and_record_lines(char *ptr, char *ptrlim, struct line **line, char *line_start, 
                                   size_t *avail, size_t line_bytes, size_t *mergesize, 
                                   struct keyfield const *key, char eol)
{
    char *p;
    while ((p = memchr(ptr, eol, ptrlim - ptr)))
    {
        ptr = p + 1;
        (*line)--;
        process_line(*line, line_start, ptr, mergesize, key, p);
        *avail -= line_bytes;
        line_start = ptr;
    }
    return line_start;
}

static void move_unused_data(struct buffer *buf)
{
    if (buf->used != buf->left)
    {
        memmove(buf->buf, buf->buf + buf->used - buf->left, buf->left);
        buf->used = buf->left;
        buf->nlines = 0;
    }
}

static void expand_buffer(struct buffer *buf)
{
    idx_t line_alloc = buf->alloc / sizeof(struct line);
    buf->buf = xpalloc(buf->buf, &line_alloc, 1, -1, sizeof(struct line));
    buf->alloc = line_alloc * sizeof(struct line);
}

static bool fillbuf(struct buffer *buf, FILE *fp, char const *file)
{
    #define MIN_AVAIL_FOR_READ 2
    
    struct keyfield const *key = keylist;
    char eol = eolchar;
    size_t line_bytes = buf->line_bytes;
    size_t mergesize = merge_buffer_size - MIN_MERGE_BUFFER_SIZE;

    if (buf->eof)
        return false;

    move_unused_data(buf);

    while (true)
    {
        char *ptr = buf->buf + buf->used;
        struct line *linelim = buffer_linelim(buf);
        struct line *line = linelim - buf->nlines;
        size_t avail = (char *)linelim - buf->nlines * line_bytes - ptr;
        char *line_start = buf->nlines ? line->text + line->length : buf->buf;

        while (line_bytes + MIN_AVAIL_FOR_READ <= avail)
        {
            size_t bytes_read = read_input_chunk(fp, ptr, avail, line_bytes);
            char *ptrlim = ptr + bytes_read;
            avail -= bytes_read;

            if (bytes_read != (avail - 1) / (line_bytes + 1))
            {
                if (check_eof_conditions(buf, fp, file, ptrlim, line_start, eol))
                    return false;
            }

            line_start = find_and_record_lines(ptr, ptrlim, &line, line_start, 
                                              &avail, line_bytes, &mergesize, key, eol);
            ptr = ptrlim;
            if (buf->eof)
                break;
        }

        buf->used = ptr - buf->buf;
        buf->nlines = buffer_linelim(buf) - line;
        
        if (buf->nlines != 0)
        {
            buf->left = ptr - line_start;
            merge_buffer_size = mergesize + MIN_MERGE_BUFFER_SIZE;
            return true;
        }

        expand_buffer(buf);
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
static char update_max_digit(char current, char max_digit)
{
    return (current > max_digit) ? current : max_digit;
}

static char const* skip_thousands_separator(char const *p)
{
    if (*p == thousands_sep)
        return p + 1;
    return p;
}

static char scan_integer_part(char const **p, char *max_digit)
{
    char ch;
    bool ends_with_thousands_sep = false;
    
    while (c_isdigit(ch = **p))
    {
        *max_digit = update_max_digit(ch, *max_digit);
        (*p)++;
        
        ends_with_thousands_sep = (**p == thousands_sep);
        if (ends_with_thousands_sep)
            (*p)++;
    }
    
    if (ends_with_thousands_sep)
    {
        (*p) -= 2;
        return '\0';
    }
    
    return ch;
}

static void scan_decimal_part(char const **p, char *max_digit)
{
    char ch;
    
    if (**p != decimal_point)
        return;
    
    (*p)++;
    
    while (c_isdigit(ch = **p))
    {
        *max_digit = update_max_digit(ch, *max_digit);
        (*p)++;
    }
}

static char traverse_raw_number(char const **number)
{
    char const *p = *number;
    char max_digit = '\0';
    
    char last_char = scan_integer_part(&p, &max_digit);
    
    if (last_char == '\0')
    {
        *number = p;
        return max_digit;
    }
    
    scan_decimal_part(&p, &max_digit);
    
    *number = p - 1;
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
  bool minus_sign = (*number == '-');
  char const *p = number + minus_sign;
  char max_digit = traverse_raw_number (&p);
  
  if (max_digit <= '0')
    return 0;
    
  unsigned char ch = *p;
  int order = unit_order[ch];
  return minus_sign ? -order : order;
}

/* Compare numbers A and B ending in units with SI or IEC prefixes
       <none/unknown> < K/k < M < G < T < P < E < Z < Y < R < Q */

ATTRIBUTE_PURE
static int
human_numcompare (char const *a, char const *b)
{
  char const *trimmed_a = skip_blanks(a);
  char const *trimmed_b = skip_blanks(b);

  int diff = find_unit_order (trimmed_a) - find_unit_order (trimmed_b);
  return (diff ? diff : strnumcmp (trimmed_a, trimmed_b, decimal_point, thousands_sep));
}

static char const *
skip_blanks(char const *str)
{
  while (blanks[to_uchar (*str)])
    str++;
  return str;
}

/* Compare strings A and B as numbers without explicitly converting them to
   machine numbers.  Comparatively slow for short strings, but asymptotically
   hideously fast. */

ATTRIBUTE_PURE
static int
numcompare (char const *a, char const *b)
{
  a = skip_blanks(a);
  b = skip_blanks(b);
  return strnumcmp (a, b, decimal_point, thousands_sep);
}

static char const *
skip_blanks(char const *str)
{
  while (blanks[to_uchar (*str)])
    str++;
  return str;
}

static int
nan_compare (long double a, long double b)
{
  const size_t BUFFER_SIZE = sizeof "-nan""()" + CHAR_BIT * sizeof a;
  char buf[2][BUFFER_SIZE];
  snprintf (buf[0], BUFFER_SIZE, "%Lf", a);
  snprintf (buf[1], BUFFER_SIZE, "%Lf", b);
  return strcmp (buf[0], buf[1]);
}

static int handle_conversion_errors(char const *sa, char const *ea, char const *sb, char const *eb)
{
    if (sa == ea)
        return sb == eb ? 0 : -1;
    if (sb == eb)
        return 1;
    return 2;
}

static int compare_valid_numbers(long double a, long double b)
{
    if (a < b)
        return -1;
    if (a > b)
        return 1;
    if (a == b)
        return 0;
    if (b == b)
        return -1;
    if (a == a)
        return 1;
    return nan_compare(a, b);
}

static int general_numcompare(char const *sa, char const *sb)
{
    char *ea;
    char *eb;
    long double a = strtold(sa, &ea);
    long double b = strtold(sb, &eb);

    int error_result = handle_conversion_errors(sa, ea, sb, eb);
    if (error_result != 2)
        return error_result;

    return compare_valid_numbers(a, b);
}

/* Return an integer in 1..12 of the month name MONTH.
   Return 0 if the name in S is not recognized.  */

static int
getmonth (char const *month, char **ea)
{
  size_t lo = 0;
  size_t hi = MONTHS_PER_YEAR;

  month = skip_blanks(month);

  while (lo < hi)
    {
      size_t ix = (lo + hi) / 2;
      int cmp = compare_month_name(month, monthtab[ix].name, ea);
      
      if (cmp == 0)
        return monthtab[ix].val;
      else if (cmp < 0)
        hi = ix;
      else
        lo = ix + 1;
    }

  return 0;
}

static char const *
skip_blanks(char const *str)
{
  while (blanks[to_uchar (*str)])
    str++;
  return str;
}

static int
compare_month_name(char const *input, char const *table_name, char **end_ptr)
{
  char const *m = input;
  char const *n = table_name;

  while (*n)
    {
      unsigned char m_upper = to_uchar (fold_toupper[to_uchar (*m)]);
      unsigned char n_char = to_uchar (*n);
      
      if (m_upper < n_char)
        return -1;
      if (m_upper > n_char)
        return 1;
      
      m++;
      n++;
    }
  
  if (end_ptr)
    *end_ptr = (char *) m;
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
  if (!handle)
    link_failure ();
  ptr_MD5_Init = symbol_address (handle, "MD5_Init");
  ptr_MD5_Update = symbol_address (handle, "MD5_Update");
  ptr_MD5_Final = symbol_address (handle, "MD5_Final");
#endif
}

/* A randomly chosen MD5 state, used for random comparison.  */
static struct md5_ctx random_md5_state;

/* Initialize the randomly chosen MD5 state.  */

static void
random_md5_state_init (char const *random_source)
{
  unsigned char buf[MD5_DIGEST_SIZE];
  struct randread_source *r = randread_new (random_source, sizeof buf);
  if (! r)
    sort_die (_("open failed"), random_source ? random_source : "getrandom");
  randread (r, buf, sizeof buf);
  if (randread_free (r) != 0)
    sort_die (_("close failed"), random_source);
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

static int calculate_xfrm_diff(const char *buf1, size_t size1, const char *buf2, size_t size2)
{
    int diff = memcmp(buf1, buf2, MIN(size1, size2));
    if (!diff)
        diff = _GL_CMP(size1, size2);
    return diff;
}

static size_t transform_string(char *dest, const char *src, const char *limit, size_t bufsize)
{
    if (src < limit)
        return xstrxfrm(dest, src, bufsize) + 1;
    return 0;
}

static void resize_buffer(char **buf, size_t *bufsize, void **allocated, size_t needed_size)
{
    *bufsize = needed_size;
    if (*bufsize < SIZE_MAX / 3)
        *bufsize = *bufsize * 3 / 2;
    free(*allocated);
    *buf = *allocated = xmalloc(*bufsize);
}

static void ensure_buffer_capacity(char **buf, size_t *bufsize, void **allocated, 
                                   size_t guess_size, char *stackbuf, size_t stacksize)
{
    if (*bufsize < guess_size)
    {
        *bufsize = MAX(guess_size, *bufsize * 3 / 2);
        free(*allocated);
        *buf = *allocated = malloc(*bufsize);
        if (!*buf)
        {
            *buf = stackbuf;
            *bufsize = stacksize;
        }
    }
}

static void transform_and_store(char *buf, size_t bufsize, const char *texta, const char *textb,
                                size_t *sizea, size_t *sizeb)
{
    if (texta)
        strxfrm(buf, texta, *sizea);
    if (textb)
        strxfrm(buf + *sizea, textb, *sizeb);
}

static void process_transform_iteration(char **texta, size_t *lena, const char *lima,
                                       char **textb, size_t *lenb, const char *limb,
                                       char **buf, size_t *bufsize, void **allocated,
                                       struct md5_ctx *s, int *xfrm_diff,
                                       char *stackbuf, size_t stacksize)
{
    size_t guess_bufsize = 3 * (*lena + *lenb) + 2;
    ensure_buffer_capacity(buf, bufsize, allocated, guess_bufsize, stackbuf, stacksize);
    
    size_t sizea = transform_string(*buf, *texta, lima, *bufsize);
    bool a_fits = sizea <= *bufsize;
    size_t sizeb = transform_string(a_fits ? *buf + sizea : nullptr, *textb, limb,
                                   a_fits ? *bufsize - sizea : 0);
    
    if (!(a_fits && sizea + sizeb <= *bufsize))
    {
        resize_buffer(buf, bufsize, allocated, sizea + sizeb);
        transform_and_store(*buf, *bufsize, *texta < lima ? *texta : nullptr,
                           *textb < limb ? *textb : nullptr, &sizea, &sizeb);
    }
    
    if (*texta < lima)
        *texta += strlen(*texta) + 1;
    if (*textb < limb)
        *textb += strlen(*textb) + 1;
    
    if (!(*texta < lima || *textb < limb))
    {
        *lena = sizea;
        *texta = *buf;
        *lenb = sizeb;
        *textb = *buf + sizea;
        return;
    }
    
    md5_process_bytes(*buf, sizea, &s[0]);
    md5_process_bytes(*buf + sizea, sizeb, &s[1]);
    
    if (!*xfrm_diff)
        *xfrm_diff = calculate_xfrm_diff(*buf, sizea, *buf + sizea, sizeb);
}

static void compute_checksums(const char *texta, size_t lena, const char *textb, size_t lenb,
                              struct md5_ctx *s, uint32_t dig[2][MD5_DIGEST_SIZE / sizeof(uint32_t)])
{
    md5_process_bytes(texta, lena, &s[0]);
    md5_finish_ctx(&s[0], dig[0]);
    md5_process_bytes(textb, lenb, &s[1]);
    md5_finish_ctx(&s[1], dig[1]);
}

static int compare_random(char *restrict texta, size_t lena,
                         char *restrict textb, size_t lenb)
{
    #define STACK_BUFFER_SIZE 4000
    
    int xfrm_diff = 0;
    char stackbuf[STACK_BUFFER_SIZE];
    char *buf = stackbuf;
    size_t bufsize = sizeof stackbuf;
    void *allocated = nullptr;
    uint32_t dig[2][MD5_DIGEST_SIZE / sizeof(uint32_t)];
    struct md5_ctx s[2];
    s[0] = s[1] = random_md5_state;
    
    if (hard_LC_COLLATE)
    {
        char const *lima = texta + lena;
        char const *limb = textb + lenb;
        
        while (true)
        {
            process_transform_iteration(&texta, &lena, lima, &textb, &lenb, limb,
                                       &buf, &bufsize, &allocated, s, &xfrm_diff,
                                       stackbuf, STACK_BUFFER_SIZE);
            if (!(texta < lima || textb < limb))
                break;
        }
    }
    
    compute_checksums(texta, lena, textb, lenb, s, dig);
    int diff = memcmp(dig[0], dig[1], sizeof dig[0]);
    
    if (!diff)
    {
        if (!xfrm_diff)
            xfrm_diff = calculate_xfrm_diff(texta, lena, textb, lenb);
        diff = xfrm_diff;
    }
    
    free(allocated);
    return diff;
}

/* Return the printable width of the block of memory starting at
   TEXT and ending just before LIM, counting each tab as one byte.
   FIXME: Should we generally be counting non printable chars?  */

static size_t debug_width(char const *text, char const *lim)
{
    size_t width = mbsnwidth(text, lim - text, 0);
    size_t tab_count = 0;
    
    while (text < lim) {
        if (*text == '\t') {
            tab_count++;
        }
        text++;
    }
    
    return width + tab_count;
}

/* For debug mode, "underline" a key at the
   specified offset and screen width.  */

static void print_spaces(size_t count)
{
    while (count--)
        putchar(' ');
}

static void print_underscores(size_t count)
{
    while (count--)
        putchar('_');
}

static void mark_key(size_t offset, size_t width)
{
    print_spaces(offset);

    if (!width)
        printf(_("^ no match for key\n"));
    else
    {
        print_underscores(width);
        putchar('\n');
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

static void skip_leading_blanks(char **beg, char *lim)
{
    while (*beg < lim && blanks[to_uchar (**beg)])
        (*beg)++;
}

static char *get_numeric_limit(char *beg, char *lim, struct keyfield const *key)
{
    char const *p = beg + (beg < lim && *beg == '-');
    char max_digit = traverse_raw_number(&p);
    if ('0' <= max_digit)
    {
        unsigned char ch = *p;
        return (char *) p + (key->human_numeric && unit_order[ch]);
    }
    return lim;
}

static char *calculate_tighter_limit(char *beg, char *lim, struct keyfield const *key)
{
    if (lim < beg)
        return lim;
    
    if (key->month)
    {
        char *tighter_lim = beg;
        getmonth(beg, &tighter_lim);
        return tighter_lim;
    }
    
    if (key->general_numeric)
    {
        char *tighter_lim = beg;
        ignore_value(strtold(beg, &tighter_lim));
        return tighter_lim;
    }
    
    if (key->numeric || key->human_numeric)
        return get_numeric_limit(beg, lim, key);
    
    return lim;
}

static void adjust_field_boundaries(char **beg, char **lim, struct keyfield const *key)
{
    if ((key->skipsblanks && key->sword == SIZE_MAX) || key->month || key_numeric(key))
    {
        char saved = **lim;
        **lim = '\0';
        
        skip_leading_blanks(beg, *lim);
        char *tighter_lim = calculate_tighter_limit(*beg, *lim, key);
        
        **lim = saved;
        *lim = tighter_lim;
    }
}

static void get_field_boundaries(struct line const *line, struct keyfield const *key, char **beg, char **lim)
{
    char *text = line->text;
    *beg = text;
    *lim = text + line->length - 1;
    
    if (!key)
        return;
    
    if (key->sword != SIZE_MAX)
        *beg = begfield(line, key);
    
    if (key->eword != SIZE_MAX)
    {
        *lim = limfield(line, key);
        *lim = MAX(*beg, *lim);
    }
    
    adjust_field_boundaries(beg, lim, key);
}

static void debug_key(struct line const *line, struct keyfield const *key)
{
    char *beg, *lim;
    get_field_boundaries(line, key, &beg, &lim);
    
    size_t offset = debug_width(line->text, beg);
    size_t width = debug_width(beg, lim);
    mark_key(offset, width);
}

/* Debug LINE by underlining its keys.  */

static void
debug_line (struct line const *line)
{
  struct keyfield const *key = keylist;

  do
    debug_key (line, key);
  while (key && ((key = key->next) || ! (unique || stable)));
}

/* Return whether sorting options specified for key.  */

static bool
default_key_compare (struct keyfield const *key)
{
  return ! (key->ignore
            || key->translate
            || key->skipsblanks
            || key->skipeblanks
            || key_numeric (key)
            || key->month
            || key->version
            || key->random);
}

/* Convert a key to the short options used to specify it.  */

static void
key_to_opts (struct keyfield const *key, char *opts)
{
  if (key->skipsblanks || key->skipeblanks)
    *opts++ = 'b';
  if (key->ignore == nondictionary)
    *opts++ = 'd';
  if (key->translate)
    *opts++ = 'f';
  if (key->general_numeric)
    *opts++ = 'g';
  if (key->human_numeric)
    *opts++ = 'h';
  if (key->ignore == nonprinting)
    *opts++ = 'i';
  if (key->month)
    *opts++ = 'M';
  if (key->numeric)
    *opts++ = 'n';
  if (key->random)
    *opts++ = 'R';
  if (key->reverse)
    *opts++ = 'r';
  if (key->version)
    *opts++ = 'V';
  *opts = '\0';
}

/* Output data independent key warnings to stderr.  */

static void warn_obsolescent_syntax(struct keyfield const *key)
{
    size_t sword = key->sword;
    size_t eword = key->eword;
    char tmp[INT_BUFSIZE_BOUND (uintmax_t)];
    char obuf[INT_BUFSIZE_BOUND (sword) * 2 + 4];
    char nbuf[INT_BUFSIZE_BOUND (sword) * 2 + 5];
    char *po = obuf;
    char *pn = nbuf;

    if (sword == SIZE_MAX)
        sword++;

    po = stpcpy (stpcpy (po, "+"), umaxtostr (sword, tmp));
    pn = stpcpy (stpcpy (pn, "-k "), umaxtostr (sword + 1, tmp));
    if (key->eword != SIZE_MAX)
    {
        stpcpy (stpcpy (po, " -"), umaxtostr (eword + 1, tmp));
        stpcpy (stpcpy (pn, ","),
                umaxtostr (eword + 1 + (key->echar == SIZE_MAX), tmp));
    }
    error (0, 0, _("obsolescent key %s used; consider %s instead"),
           quote_n (0, obuf), quote_n (1, nbuf));
}

static bool check_zero_width(struct keyfield const *key, unsigned long keynum)
{
    bool zero_width = key->sword != SIZE_MAX && key->eword < key->sword;
    if (zero_width)
        error (0, 0, _("key %lu has zero width and will be ignored"), keynum);
    return zero_width;
}

static void warn_leading_blanks(struct keyfield const *key, unsigned long keynum, 
                                bool zero_width, bool gkey_only)
{
    bool implicit_skip = key_numeric (key) || key->month;
    bool line_offset = key->eword == 0 && key->echar != 0;
    
    if (!zero_width && !gkey_only && tab == TAB_DEFAULT && !line_offset
        && ((!key->skipsblanks && !implicit_skip)
            || (!key->skipsblanks && key->schar)
            || (!key->skipeblanks && key->echar)))
        error (0, 0, _("leading blanks are significant in key %lu; "
                     "consider also specifying 'b'"), keynum);
}

static void check_numeric_span(struct keyfield const *key, unsigned long keynum,
                               bool gkey_only, bool *general_numeric_field_span,
                               bool *basic_numeric_field_span)
{
    if (!gkey_only && key_numeric (key))
    {
        size_t sword = key->sword + 1;
        size_t eword = key->eword + 1;
        if (!sword)
            sword++;
        if (!eword || sword < eword)
        {
            error (0, 0, _("key %lu is numeric and spans multiple fields"),
                   keynum);
            if (key->general_numeric)
                *general_numeric_field_span = true;
            else
                *basic_numeric_field_span = true;
        }
    }
}

static void update_global_flags(struct keyfield *ugkey, struct keyfield const *key)
{
    if (ugkey->ignore && (ugkey->ignore == key->ignore))
        ugkey->ignore = nullptr;
    if (ugkey->translate && (ugkey->translate == key->translate))
        ugkey->translate = nullptr;
    ugkey->skipsblanks &= !key->skipsblanks;
    ugkey->skipeblanks &= !key->skipeblanks;
    ugkey->month &= !key->month;
    ugkey->numeric &= !key->numeric;
    ugkey->general_numeric &= !key->general_numeric;
    ugkey->human_numeric &= !key->human_numeric;
    ugkey->random &= !key->random;
    ugkey->version &= !key->version;
    ugkey->reverse &= !key->reverse;
}

static bool warn_thousands_separator(bool basic_numeric_field_span)
{
    if (basic_numeric_field_span)
    {
        if (tab == TAB_DEFAULT
            ? thousands_sep != NON_CHAR && (isblank (to_uchar (thousands_sep)))
            : tab == thousands_sep)
        {
            error (0, 0,
                   _("field separator %s is treated as a "
                     "group separator in numbers"),
                   quote (((char []) {thousands_sep, 0})));
            return true;
        }
    }
    return false;
}

static bool warn_decimal_point_separator(bool basic_numeric_field_span, 
                                        bool general_numeric_field_span)
{
    if (basic_numeric_field_span || general_numeric_field_span)
    {
        if (tab == TAB_DEFAULT
            ? thousands_sep != NON_CHAR && (isblank (to_uchar (decimal_point)))
            : tab == decimal_point)
        {
            error (0, 0,
                   _("field separator %s is treated as a "
                     "decimal point in numbers"),
                   quote (((char []) {decimal_point, 0})));
            return true;
        }
    }
    return false;
}

static void warn_sign_separators(bool basic_numeric_field_span,
                                bool general_numeric_field_span)
{
    if ((basic_numeric_field_span || general_numeric_field_span) && tab == '-')
    {
        error (0, 0,
               _("field separator %s is treated as a "
                 "minus sign in numbers"),
               quote (((char []) {tab, 0})));
    }
    else if (general_numeric_field_span && tab == '+')
    {
        error (0, 0,
               _("field separator %s is treated as a "
                 "plus sign in numbers"),
               quote (((char []) {tab, 0})));
    }
}

static void warn_field_separators(bool basic_numeric_field_span,
                                 bool general_numeric_field_span,
                                 bool *number_locale_warned)
{
    *number_locale_warned = warn_thousands_separator(basic_numeric_field_span);
    *number_locale_warned |= warn_decimal_point_separator(basic_numeric_field_span,
                                                         general_numeric_field_span);
    warn_sign_separators(basic_numeric_field_span, general_numeric_field_span);
}

static void warn_locale_settings(bool basic_numeric_field, bool general_numeric_field,
                                bool number_locale_warned)
{
    if ((basic_numeric_field || general_numeric_field) && !number_locale_warned)
    {
        error (0, 0,
               _("numbers use %s as a decimal point in this locale"),
               quote (((char []) {decimal_point, 0})));
    }

    if (basic_numeric_field && thousands_sep_ignored)
    {
        error (0, 0,
               _("the multi-byte number group separator "
                 "in this locale is not supported"));
    }
}

static void warn_ignored_global_options(struct keyfield *ugkey)
{
    if (!default_key_compare (ugkey)
        || (ugkey->reverse && (stable || unique) && keylist))
    {
        bool ugkey_reverse = ugkey->reverse;
        if (!(stable || unique))
            ugkey->reverse = false;
        char opts[sizeof short_options];
        key_to_opts (ugkey, opts);
        error (0, 0,
               ngettext ("option '-%s' is ignored",
                        "options '-%s' are ignored",
                        select_plural (strlen (opts))), opts);
        ugkey->reverse = ugkey_reverse;
    }
    if (ugkey->reverse && !(stable || unique) && keylist)
        error (0, 0, _("option '-r' only applies to last-resort comparison"));
}

static void
key_warnings (struct keyfield const *gkey, bool gkey_only)
{
    struct keyfield const *key;
    struct keyfield ugkey = *gkey;
    unsigned long keynum = 1;
    bool basic_numeric_field = false;
    bool general_numeric_field = false;
    bool basic_numeric_field_span = false;
    bool general_numeric_field_span = false;

    for (key = keylist; key; key = key->next, keynum++)
    {
        if (key_numeric (key))
        {
            if (key->general_numeric)
                general_numeric_field = true;
            else
                basic_numeric_field = true;
        }

        if (key->traditional_used)
            warn_obsolescent_syntax(key);

        bool zero_width = check_zero_width(key, keynum);
        warn_leading_blanks(key, keynum, zero_width, gkey_only);
        check_numeric_span(key, keynum, gkey_only, 
                          &general_numeric_field_span, &basic_numeric_field_span);
        update_global_flags(&ugkey, key);
    }

    bool number_locale_warned = false;
    warn_field_separators(basic_numeric_field_span, general_numeric_field_span,
                         &number_locale_warned);
    warn_locale_settings(basic_numeric_field, general_numeric_field,
                       number_locale_warned);
    warn_ignored_global_options(&ugkey);
}

/* Return either the sense of DIFF or its reverse, depending on REVERSED.
   If REVERSED, do not simply negate DIFF as that can mishandle INT_MIN.  */

static int
diff_reversed (int diff, bool reversed)
{
  if (!reversed)
  {
    return diff;
  }
  
  if (diff > 0)
  {
    return -1;
  }
  
  if (diff < 0)
  {
    return 1;
  }
  
  return 0;
}

/* Compare two lines A and B trying every key in sequence until there
   are no more keys or a difference is found. */

static int compare_with_translation(const char *texta, const char *textb, 
                                    size_t lena, size_t lenb, 
                                    const char *translate)
{
    size_t lenmin = MIN(lena, lenb);
    if (lenmin == 0)
        return 0;
    
    int diff = 0;
    for (size_t i = 0; i < lenmin; i++) {
        diff = (to_uchar(translate[to_uchar(texta[i])])
                - to_uchar(translate[to_uchar(textb[i])]));
        if (diff)
            return diff;
    }
    return _GL_CMP(lena, lenb);
}

static int compare_simple(const char *texta, const char *textb, 
                          size_t lena, size_t lenb)
{
    size_t lenmin = MIN(lena, lenb);
    if (lenmin == 0)
        return 0;
    
    int diff = memcmp(texta, textb, lenmin);
    if (!diff)
        diff = _GL_CMP(lena, lenb);
    return diff;
}

static void copy_with_transform(char *dest, size_t *destlen,
                                const char *src, size_t srclen,
                                const char *translate, const bool *ignore)
{
    size_t j = 0;
    for (size_t i = 0; i < srclen; i++) {
        if (!(ignore && ignore[to_uchar(src[i])])) {
            dest[j++] = translate ? translate[to_uchar(src[i])] : src[i];
        }
    }
    *destlen = j;
}

static char* allocate_buffer(size_t size, char *stackbuf, size_t stacksize)
{
    if (size <= stacksize)
        return stackbuf;
    return xmalloc(size);
}

static int compare_with_ignore(char **texta_ptr, char **textb_ptr,
                               char *lima, char *limb,
                               const char *translate, const bool *ignore)
{
    char *texta = *texta_ptr;
    char *textb = *textb_ptr;
    
    while (true) {
        while (texta < lima && ignore[to_uchar(*texta)])
            ++texta;
        while (textb < limb && ignore[to_uchar(*textb)])
            ++textb;
        
        if (!(texta < lima && textb < limb))
            return (texta < lima) - (textb < limb);
        
        int diff = translate 
            ? to_uchar(translate[to_uchar(*texta)]) - to_uchar(translate[to_uchar(*textb)])
            : to_uchar(*texta) - to_uchar(*textb);
        
        if (diff)
            return diff;
        
        ++texta;
        ++textb;
    }
}

static int perform_special_comparison(const struct keyfield *key,
                                      const char *ta, const char *tb,
                                      size_t tlena, size_t tlenb)
{
    if (key->numeric)
        return numcompare(ta, tb);
    if (key->general_numeric)
        return general_numcompare(ta, tb);
    if (key->human_numeric)
        return human_numcompare(ta, tb);
    if (key->month)
        return getmonth(ta, nullptr) - getmonth(tb, nullptr);
    if (key->random)
        return compare_random(ta, tlena, tb, tlenb);
    if (key->version)
        return filenvercmp(ta, tlena, tb, tlenb);
    
    if (tlena == 0)
        return -NONZERO(tlenb);
    if (tlenb == 0)
        return 1;
    return xmemcoll0(ta, tlena + 1, tb, tlenb + 1);
}

static int compare_with_special_handling(const struct keyfield *key,
                                         char *texta, char *textb,
                                         size_t lena, size_t lenb)
{
    char *ta = texta;
    char *tb = textb;
    size_t tlena = lena;
    size_t tlenb = lenb;
    char enda = ta[tlena];
    char endb = tb[tlenb];
    
    void *allocated = nullptr;
    char stackbuf[4000];
    
    if (key->ignore || key->translate) {
        size_t size = lena + 1 + lenb + 1;
        ta = allocate_buffer(size, stackbuf, sizeof stackbuf);
        allocated = (ta == stackbuf) ? nullptr : ta;
        tb = ta + lena + 1;
        
        copy_with_transform(ta, &tlena, texta, lena, key->translate, key->ignore);
        copy_with_transform(tb, &tlenb, textb, lenb, key->translate, key->ignore);
    }
    
    ta[tlena] = '\0';
    tb[tlenb] = '\0';
    
    int diff = perform_special_comparison(key, ta, tb, tlena, tlenb);
    
    ta[tlena] = enda;
    tb[tlenb] = endb;
    
    free(allocated);
    return diff;
}

static void update_field_positions(const struct keyfield *key,
                                   const struct line *a, const struct line *b,
                                   char **texta, char **textb,
                                   char **lima, char **limb)
{
    if (key->eword != SIZE_MAX) {
        *lima = limfield(a, key);
        *limb = limfield(b, key);
    } else {
        *lima = a->text + a->length - 1;
        *limb = b->text + b->length - 1;
    }
    
    if (key->sword != SIZE_MAX) {
        *texta = begfield(a, key);
        *textb = begfield(b, key);
    } else {
        *texta = a->text;
        *textb = b->text;
        if (key->skipsblanks) {
            while (*texta < *lima && blanks[to_uchar(**texta)])
                ++(*texta);
            while (*textb < *limb && blanks[to_uchar(**textb)])
                ++(*textb);
        }
    }
}

static int
keycompare(struct line const *a, struct line const *b)
{
    struct keyfield *key = keylist;
    
    char *texta = a->keybeg;
    char *textb = b->keybeg;
    char *lima = a->keylim;
    char *limb = b->keylim;
    
    int diff;
    
    while (true) {
        lima = MAX(texta, lima);
        limb = MAX(textb, limb);
        
        size_t lena = lima - texta;
        size_t lenb = limb - textb;
        
        if (hard_LC_COLLATE || key_numeric(key)
            || key->month || key->random || key->version) {
            diff = compare_with_special_handling(key, texta, textb, lena, lenb);
        } else if (key->ignore) {
            diff = compare_with_ignore(&texta, &textb, lima, limb, 
                                       key->translate, key->ignore);
        } else {
            diff = key->translate 
                ? compare_with_translation(texta, textb, lena, lenb, key->translate)
                : compare_simple(texta, textb, lena, lenb);
        }
        
        if (diff)
            break;
        
        key = key->next;
        if (!key)
            return 0;
        
        update_field_positions(key, a, b, &texta, &textb, &lima, &limb);
    }
    
    return diff_reversed(diff, key->reverse);
}

/* Compare two lines A and B, returning negative, zero, or positive
   depending on whether A compares less than, equal to, or greater than B. */

static int compare_with_keys(struct line const *a, struct line const *b)
{
    int diff = keycompare(a, b);
    if (diff || unique || stable)
        return diff;
    return 0;
}

static int compare_empty_lines(size_t alen, size_t blen)
{
    if (alen == 0)
        return -NONZERO(blen);
    if (blen == 0)
        return 1;
    return 0;
}

static int compare_with_collation(struct line const *a, struct line const *b, size_t alen, size_t blen)
{
    return xmemcoll0(a->text, alen + 1, b->text, blen + 1);
}

static int compare_binary(struct line const *a, struct line const *b, size_t alen, size_t blen)
{
    int diff = memcmp(a->text, b->text, MIN(alen, blen));
    if (!diff)
        diff = _GL_CMP(alen, blen);
    return diff;
}

static int compare_default(struct line const *a, struct line const *b)
{
    size_t alen = a->length - 1;
    size_t blen = b->length - 1;
    
    int diff = compare_empty_lines(alen, blen);
    if (diff)
        return diff;
    
    if (hard_LC_COLLATE)
        return compare_with_collation(a, b, alen, blen);
    
    return compare_binary(a, b, alen, blen);
}

static int compare(struct line const *a, struct line const *b)
{
    int diff = 0;
    
    if (keylist)
    {
        diff = compare_with_keys(a, b);
        if (diff)
            return diff;
    }
    
    diff = compare_default(a, b);
    return diff_reversed(diff, reverse);
}

/* Write LINE to output stream FP; the output file's name is
   OUTPUT_FILE if OUTPUT_FILE is non-null, and is the standard output
   otherwise.  If debugging is enabled and FP is standard output,
   append some debugging information.  */

static void write_debug_char(char c, char const *ebuf, FILE *fp, char const *output_file)
{
    char wc = c;
    if (wc == '\t')
        wc = '>';
    else if (&c == ebuf - 1)
        wc = '\n';
    if (fputc(wc, fp) == EOF)
        sort_die(_("write failed"), output_file);
}

static void write_debug_mode(struct line const *line, FILE *fp, char const *output_file)
{
    char *buf = line->text;
    size_t n_bytes = line->length;
    char *ebuf = buf + n_bytes;
    char const *c = buf;

    while (c < ebuf)
    {
        write_debug_char(*c, ebuf, fp, output_file);
        c++;
    }
    debug_line(line);
}

static void write_normal_mode(struct line const *line, FILE *fp, char const *output_file)
{
    char *buf = line->text;
    size_t n_bytes = line->length;
    char *ebuf = buf + n_bytes;
    
    ebuf[-1] = eolchar;
    if (fwrite(buf, 1, n_bytes, fp) != n_bytes)
        sort_die(_("write failed"), output_file);
    ebuf[-1] = '\0';
}

static void write_line(struct line const *line, FILE *fp, char const *output_file)
{
    if (!output_file && debug)
        write_debug_mode(line, fp, output_file);
    else
        write_normal_mode(line, fp, output_file);
}

/* Check that the lines read from FILE_NAME come in order.  Return
   true if they are in order.  If CHECKONLY == 'c', also print a
   diagnostic (FILE_NAME, line number, contents of line) to stderr if
   they are not in order.  */

static bool is_disorder_detected(struct line const *temp, struct line const *line, bool nonunique)
{
    return nonunique <= compare(temp, line);
}

static void report_disorder(char const *file_name, struct line const *disorder_line, 
                           struct buffer const *buf, uintmax_t line_number)
{
    uintmax_t disorder_line_number = buffer_linelim(buf) - disorder_line + line_number;
    char hr_buf[INT_BUFSIZE_BOUND(disorder_line_number)];
    fprintf(stderr, _("%s: %s:%s: disorder: "),
            program_name, file_name,
            umaxtostr(disorder_line_number, hr_buf));
    write_line(disorder_line, stderr, _("standard error"));
}

static bool check_line_order(struct line const *linebase, struct line const *line, bool nonunique)
{
    while (linebase < --line)
    {
        if (is_disorder_detected(line, line - 1, nonunique))
            return false;
    }
    return true;
}

static size_t calculate_new_alloc(size_t current_alloc, size_t required_length)
{
    size_t new_alloc = current_alloc;
    do
    {
        new_alloc *= 2;
        if (!new_alloc)
        {
            new_alloc = required_length;
            break;
        }
    }
    while (new_alloc < required_length);
    return new_alloc;
}

static void save_line_to_temp(struct line *temp, struct line const *line, 
                              size_t *alloc, struct keyfield const *key)
{
    if (*alloc < line->length)
    {
        *alloc = calculate_new_alloc(*alloc, line->length);
        free(temp->text);
        temp->text = xmalloc(*alloc);
    }
    memcpy(temp->text, line->text, line->length);
    temp->length = line->length;
    if (key)
    {
        temp->keybeg = temp->text + (line->keybeg - line->text);
        temp->keylim = temp->text + (line->keylim - line->text);
    }
}

static bool
check(char const *file_name, char checkonly)
{
    FILE *fp = xfopen(file_name, "r");
    struct buffer buf;
    struct line temp;
    size_t alloc = 0;
    uintmax_t line_number = 0;
    struct keyfield const *key = keylist;
    bool nonunique = !unique;
    bool ordered = true;

    initbuf(&buf, sizeof(struct line),
            MAX(merge_buffer_size, sort_size));
    temp.text = nullptr;

    while (fillbuf(&buf, fp, file_name))
    {
        struct line const *line = buffer_linelim(&buf);
        struct line const *linebase = line - buf.nlines;

        if (alloc && is_disorder_detected(&temp, line - 1, nonunique))
        {
            if (checkonly == 'c')
            {
                report_disorder(file_name, line - 1, &buf, line_number);
            }
            ordered = false;
            break;
        }

        if (!check_line_order(linebase, line, nonunique))
        {
            if (checkonly == 'c')
            {
                report_disorder(file_name, line - 1, &buf, line_number);
            }
            ordered = false;
            break;
        }

        line_number += buf.nlines;
        save_line_to_temp(&temp, line, &alloc, key);
    }

    xfclose(fp, file_name);
    free(buf.buf);
    free(temp.text);
    return ordered;
}

/* Open FILES (there are NFILES of them) and store the resulting array
   of stream pointers into (*PFPS).  Allocate the array.  Return the
   number of successfully opened files, setting errno if this value is
   less than NFILES.  */

static FILE* open_single_file(struct sortfile *file)
{
    if (file->temp && file->temp->state != UNCOMPRESSED) {
        return open_temp(file->temp);
    }
    return stream_open(file->name, "r");
}

static size_t open_input_files(struct sortfile *files, size_t nfiles, FILE ***pfps)
{
    FILE **fps = *pfps = xnmalloc(nfiles, sizeof *fps);
    size_t i;

    for (i = 0; i < nfiles; i++) {
        fps[i] = open_single_file(&files[i]);
        if (!fps[i]) {
            break;
        }
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

static void initialize_buffers(struct buffer **buffer, struct line const ***cur,
                               struct line const ***base, size_t **ord, size_t nfiles)
{
    *buffer = xnmalloc(nfiles, sizeof **buffer);
    *cur = xnmalloc(nfiles, sizeof **cur);
    *base = xnmalloc(nfiles, sizeof **base);
    *ord = xnmalloc(nfiles, sizeof **ord);
}

static void close_and_cleanup_file(FILE **fps, struct sortfile *files, 
                                   struct buffer *buffer, size_t i, 
                                   size_t *ntemps)
{
    xfclose(fps[i], files[i].name);
    if (i < *ntemps)
    {
        (*ntemps)--;
        zaptemp(files[i].name);
    }
    free(buffer[i].buf);
}

static void shift_arrays_left(FILE **fps, struct sortfile *files, 
                              size_t start, size_t nfiles)
{
    size_t j;
    for (j = start; j < nfiles; ++j)
    {
        files[j] = files[j + 1];
        fps[j] = fps[j + 1];
    }
}

static size_t read_initial_lines(struct buffer *buffer, FILE **fps, 
                                 struct sortfile *files, struct line const **cur,
                                 struct line const **base, size_t nfiles, 
                                 size_t ntemps)
{
    size_t i;
    for (i = 0; i < nfiles; )
    {
        initbuf(&buffer[i], sizeof(struct line),
                MAX(merge_buffer_size, sort_size / nfiles));
        if (fillbuf(&buffer[i], fps[i], files[i].name))
        {
            struct line const *linelim = buffer_linelim(&buffer[i]);
            cur[i] = linelim - 1;
            base[i] = linelim - buffer[i].nlines;
            i++;
        }
        else
        {
            close_and_cleanup_file(fps, files, buffer, i, &ntemps);
            --nfiles;
            shift_arrays_left(fps, files, i, nfiles);
        }
    }
    return nfiles;
}

static void initialize_ord_table(size_t *ord, struct line const **cur, size_t nfiles)
{
    size_t i, t;
    for (i = 0; i < nfiles; ++i)
        ord[i] = i;
    for (i = 1; i < nfiles; ++i)
        if (0 < compare(cur[ord[i - 1]], cur[ord[i]]))
            t = ord[i - 1], ord[i - 1] = ord[i], ord[i] = t, i = 0;
}

static void grow_save_buffer(struct line *saved, size_t *savealloc, size_t needed_length)
{
    if (*savealloc < needed_length)
    {
        do
            if (!*savealloc)
            {
                *savealloc = needed_length;
                break;
            }
        while ((*savealloc *= 2) < needed_length);

        free(saved->text);
        saved->text = xmalloc(*savealloc);
    }
}

static void copy_line_to_saved(struct line *saved, struct line const *smallest,
                               size_t *savealloc, struct keyfield const *key)
{
    grow_save_buffer(saved, savealloc, smallest->length);
    saved->length = smallest->length;
    memcpy(saved->text, smallest->text, saved->length);
    if (key)
    {
        saved->keybeg = saved->text + (smallest->keybeg - smallest->text);
        saved->keylim = saved->text + (smallest->keylim - smallest->text);
    }
}

static void handle_unique_output(struct line *saved, struct line const **savedline,
                                 struct line const *smallest, size_t *savealloc,
                                 FILE *ofp, char const *output_file,
                                 struct keyfield const *key)
{
    if (*savedline && compare(*savedline, smallest))
    {
        *savedline = nullptr;
        write_line(saved, ofp, output_file);
    }
    if (!*savedline)
    {
        *savedline = saved;
        copy_line_to_saved(saved, smallest, savealloc, key);
    }
}

static void remove_exhausted_file(FILE **fps, struct sortfile *files, 
                                  struct buffer *buffer, struct line const **cur,
                                  struct line const **base, size_t *ord,
                                  size_t *nfiles, size_t *ntemps)
{
    size_t i;
    for (i = 1; i < *nfiles; ++i)
        if (ord[i] > ord[0])
            --ord[i];
    
    --(*nfiles);
    xfclose(fps[ord[0]], files[ord[0]].name);
    
    if (ord[0] < *ntemps)
    {
        (*ntemps)--;
        zaptemp(files[ord[0]].name);
    }
    free(buffer[ord[0]].buf);
    
    for (i = ord[0]; i < *nfiles; ++i)
    {
        fps[i] = fps[i + 1];
        files[i] = files[i + 1];
        buffer[i] = buffer[i + 1];
        cur[i] = cur[i + 1];
        base[i] = base[i + 1];
    }
    for (i = 0; i < *nfiles; ++i)
        ord[i] = ord[i + 1];
}

static void reposition_in_queue(size_t *ord, struct line const **cur, size_t nfiles)
{
    size_t lo = 1;
    size_t hi = nfiles;
    size_t probe = lo;
    size_t ord0 = ord[0];
    size_t count_of_smaller_lines;
    size_t j;

    while (lo < hi)
    {
        int cmp = compare(cur[ord0], cur[ord[probe]]);
        if (cmp < 0 || (cmp == 0 && ord0 < ord[probe]))
            hi = probe;
        else
            lo = probe + 1;
        probe = (lo + hi) / 2;
    }

    count_of_smaller_lines = lo - 1;
    for (j = 0; j < count_of_smaller_lines; j++)
        ord[j] = ord[j + 1];
    ord[count_of_smaller_lines] = ord0;
}

static void cleanup_resources(FILE *ofp, char const *output_file, FILE **fps,
                              struct buffer *buffer, size_t *ord,
                              struct line const **base, struct line const **cur)
{
    xfclose(ofp, output_file);
    free(fps);
    free(buffer);
    free(ord);
    free(base);
    free(cur);
}

static void mergefps(struct sortfile *files, size_t ntemps, size_t nfiles,
                    FILE *ofp, char const *output_file, FILE **fps)
{
    struct buffer *buffer;
    struct line saved;
    struct line const *savedline = nullptr;
    size_t savealloc = 0;
    struct line const **cur;
    struct line const **base;
    size_t *ord;
    struct keyfield const *key = keylist;
    
    saved.text = nullptr;
    
    initialize_buffers(&buffer, &cur, &base, &ord, nfiles);
    nfiles = read_initial_lines(buffer, fps, files, cur, base, nfiles, ntemps);
    initialize_ord_table(ord, cur, nfiles);

    while (nfiles)
    {
        struct line const *smallest = cur[ord[0]];

        if (unique)
            handle_unique_output(&saved, &savedline, smallest, &savealloc, 
                               ofp, output_file, key);
        else
            write_line(smallest, ofp, output_file);

        if (base[ord[0]] < smallest)
        {
            cur[ord[0]] = smallest - 1;
        }
        else
        {
            if (fillbuf(&buffer[ord[0]], fps[ord[0]], files[ord[0]].name))
            {
                struct line const *linelim = buffer_linelim(&buffer[ord[0]]);
                cur[ord[0]] = linelim - 1;
                base[ord[0]] = linelim - buffer[ord[0]].nlines;
            }
            else
            {
                remove_exhausted_file(fps, files, buffer, cur, base, ord,
                                    &nfiles, &ntemps);
                continue;
            }
        }

        reposition_in_queue(ord, cur, nfiles);
    }

    if (unique && savedline)
    {
        write_line(&saved, ofp, output_file);
        free(saved.text);
    }

    cleanup_resources(ofp, output_file, fps, buffer, ord, base, cur);
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
  FILE **fps;
  size_t nopened = open_input_files (files, nfiles, &fps);
  
  if (nopened < nfiles && nopened < 2)
    sort_die (_("open failed"), files[nopened].name);
  
  mergefps (files, ntemps, nopened, ofp, output_file, fps);
  
  return nopened;
}

/* Merge into T (of size NLINES) the two sorted arrays of lines
   LO (with NLINES / 2 members), and
   T - (NLINES / 2) (with NLINES - NLINES / 2 members).
   T and LO point just past their respective arrays, and the arrays
   are in reverse order.  NLINES must be at least 2.  */

static void copy_remaining_lo_elements(struct line *restrict *t, struct line const *restrict *lo, size_t *nlo)
{
    do {
        *--(*t) = *--(*lo);
    } while (--(*nlo));
}

static void copy_single_element(struct line *restrict *t, struct line const *restrict *source)
{
    *--(*t) = *--(*source);
}

static void mergelines(struct line *restrict t, size_t nlines, struct line const *restrict lo)
{
    size_t nlo = nlines / 2;
    size_t nhi = nlines - nlo;
    struct line *hi = t - nlo;

    while (true) {
        if (compare(lo - 1, hi - 1) <= 0) {
            copy_single_element(&t, &lo);
            if (!--nlo) {
                return;
            }
        } else {
            copy_single_element(&t, (struct line const *restrict *)&hi);
            if (!--nhi) {
                copy_remaining_lo_elements(&t, &lo, &nlo);
                return;
            }
        }
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

static void swap_lines(struct line *restrict lines, struct line *restrict temp, int swap, bool to_temp)
{
    if (to_temp)
    {
        temp[-1] = lines[-1 - swap];
        temp[-2] = lines[-2 + swap];
    }
    else if (swap)
    {
        temp[-1] = lines[-1];
        lines[-1] = lines[-2];
        lines[-2] = temp[-1];
    }
}

static void handle_two_lines(struct line *restrict lines, struct line *restrict temp, bool to_temp)
{
    int swap = (0 < compare(&lines[-1], &lines[-2]));
    swap_lines(lines, temp, swap, to_temp);
}

static void merge_sorted_halves(struct line *restrict lines, size_t nlines, 
                                struct line *restrict temp, bool to_temp)
{
    struct line *dest = to_temp ? temp : lines;
    struct line const *sorted_lo = to_temp ? lines : temp;
    mergelines(dest, nlines, sorted_lo);
}

static void sort_lower_half(struct line *lo, size_t nlo, struct line *restrict temp, bool to_temp)
{
    if (1 < nlo)
        sequential_sort(lo, nlo, temp, !to_temp);
    else if (!to_temp)
        temp[-1] = lo[-1];
}

static void sequential_sort(struct line *restrict lines, size_t nlines,
                           struct line *restrict temp, bool to_temp)
{
    #define HALF_DIVIDER 2
    
    if (nlines == HALF_DIVIDER)
    {
        handle_two_lines(lines, temp, to_temp);
        return;
    }
    
    size_t nlo = nlines / HALF_DIVIDER;
    size_t nhi = nlines - nlo;
    struct line *lo = lines;
    struct line *hi = lines - nlo;
    
    sequential_sort(hi, nhi, temp - (to_temp ? nlo : 0), to_temp);
    sort_lower_half(lo, nlo, temp, to_temp);
    merge_sorted_halves(lines, nlines, temp, to_temp);
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
  
  initialize_root_node(root, nlines);
  init_node (root, root + 1, dest, nthreads, nlines, false);
  
  return merge_tree;
}

static void initialize_root_node(struct merge_node *root, size_t nlines)
{
  root->lo = nullptr;
  root->hi = nullptr;
  root->end_lo = nullptr;
  root->end_hi = nullptr;
  root->dest = nullptr;
  root->nlo = nlines;
  root->nhi = nlines;
  root->parent = nullptr;
  root->level = MERGE_END;
  root->queued = false;
  pthread_mutex_init (&root->lock, nullptr);
}

/* Destroy the merge tree. */
static void
merge_tree_destroy (size_t nthreads, struct merge_node *merge_tree)
{
  size_t n_nodes = nthreads * 2;
  
  for (size_t i = 0; i < n_nodes; i++)
    {
      pthread_mutex_destroy (&merge_tree[i].lock);
    }

  free (merge_tree);
}

/* Initialize a merge tree node and its descendants.  The node's
   parent is PARENT.  The node and its descendants are taken from the
   array of nodes NODE_POOL.  Their destination starts at DEST; they
   will consume NTHREADS threads.  The total number of sort lines is
   TOTAL_LINES.  IS_LO_CHILD is true if the node is the low child of
   its parent.  */

static void init_node_base(struct merge_node *node, struct line *lo, struct line *hi,
                           struct line **parent_end, size_t nlo, size_t nhi,
                           struct merge_node *parent)
{
  node->lo = node->end_lo = lo;
  node->hi = node->end_hi = hi;
  node->dest = parent_end;
  node->nlo = nlo;
  node->nhi = nhi;
  node->parent = parent;
  node->level = parent->level + 1;
  node->queued = false;
  pthread_mutex_init (&node->lock, nullptr);
}

static void calculate_line_splits(size_t nlines, size_t *nlo, size_t *nhi)
{
  *nlo = nlines / 2;
  *nhi = nlines - *nlo;
}

static struct line** get_parent_end_pointer(struct merge_node *parent, bool is_lo_child)
{
  return is_lo_child ? &parent->end_lo : &parent->end_hi;
}

static size_t get_parent_line_count(struct merge_node *parent, bool is_lo_child)
{
  return is_lo_child ? parent->nlo : parent->nhi;
}

static struct merge_node* init_child_nodes(struct merge_node *node,
                                          struct merge_node *node_pool,
                                          struct line *lo, struct line *hi,
                                          size_t nthreads, size_t total_lines)
{
  size_t lo_threads = nthreads / 2;
  size_t hi_threads = nthreads - lo_threads;
  
  node->lo_child = node_pool;
  node_pool = init_node(node, node_pool, lo, lo_threads, total_lines, true);
  
  node->hi_child = node_pool;
  node_pool = init_node(node, node_pool, hi, hi_threads, total_lines, false);
  
  return node_pool;
}

static struct merge_node *
init_node (struct merge_node *restrict parent,
           struct merge_node *restrict node_pool,
           struct line *dest, size_t nthreads,
           size_t total_lines, bool is_lo_child)
{
  size_t nlines = get_parent_line_count(parent, is_lo_child);
  size_t nlo, nhi;
  calculate_line_splits(nlines, &nlo, &nhi);
  
  struct line *lo = dest - total_lines;
  struct line *hi = lo - nlo;
  struct line **parent_end = get_parent_end_pointer(parent, is_lo_child);

  struct merge_node *node = node_pool++;
  init_node_base(node, lo, hi, parent_end, nlo, nhi, parent);

  if (nthreads > 1)
    {
      node_pool = init_child_nodes(node, node_pool, lo, hi, nthreads, total_lines);
    }
  else
    {
      node->lo_child = nullptr;
      node->hi_child = nullptr;
    }
  return node_pool;
}


/* Compare two merge nodes A and B for priority.  */

static int
compare_nodes (void const *a, void const *b)
{
  struct merge_node const *nodea = a;
  struct merge_node const *nodeb = b;
  
  if (nodea->level == nodeb->level)
  {
    size_t total_a = nodea->nlo + nodea->nhi;
    size_t total_b = nodeb->nlo + nodeb->nhi;
    return total_a < total_b;
  }
  
  return nodea->level < nodeb->level;
}

/* Lock a merge tree NODE.  */

static inline void
lock_node (struct merge_node *node)
{
  pthread_mutex_lock (&node->lock);
}

/* Unlock a merge tree NODE. */

static inline void unlock_node(struct merge_node *node)
{
    pthread_mutex_unlock(&node->lock);
}

/* Destroy merge QUEUE. */

static void
queue_destroy (struct merge_node_queue *queue)
{
  heap_free (queue->priority_queue);
  pthread_cond_destroy (&queue->cond);
  pthread_mutex_destroy (&queue->mutex);
}

/* Initialize merge QUEUE, allocating space suitable for a maximum of
   NTHREADS threads.  */

static void
queue_init (struct merge_node_queue *queue, size_t nthreads)
{
  const size_t HEAP_SIZE_MULTIPLIER = 2;
  queue->priority_queue = heap_alloc (compare_nodes, HEAP_SIZE_MULTIPLIER * nthreads);
  pthread_mutex_init (&queue->mutex, nullptr);
  pthread_cond_init (&queue->cond, nullptr);
}

/* Insert NODE into QUEUE.  The caller either holds a lock on NODE, or
   does not need to lock NODE.  */

static void
queue_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  pthread_mutex_lock (&queue->mutex);
  heap_insert (queue->priority_queue, node);
  node->queued = true;
  pthread_cond_signal (&queue->cond);
  pthread_mutex_unlock (&queue->mutex);
}

/* Pop the top node off the priority QUEUE, lock the node, return it.  */

static struct merge_node *
queue_pop (struct merge_node_queue *queue)
{
  struct merge_node *node = wait_for_node(queue);
  lock_node (node);
  node->queued = false;
  return node;
}

static struct merge_node *
wait_for_node (struct merge_node_queue *queue)
{
  struct merge_node *node;
  pthread_mutex_lock (&queue->mutex);
  while (! (node = heap_remove_top (queue->priority_queue)))
    pthread_cond_wait (&queue->cond, &queue->mutex);
  pthread_mutex_unlock (&queue->mutex);
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
  if (unique && saved_line.text && !compare(line, &saved_line))
  {
    return;
  }
  
  if (unique)
  {
    saved_line = *line;
  }
  
  write_line(line, tfp, temp_output);
}

/* Merge the lines currently available to a NODE in the binary
   merge tree.  Merge a number of lines appropriate for this merge
   level, assuming TOTAL_LINES is the total number of lines.

   If merging at the top level, send output to TFP.  TEMP_OUTPUT is
   the name of TFP, or is null if TFP is standard output.  */

static void merge_lines(struct line **lo, struct line **hi, 
                        struct line *end_lo, struct line *end_hi,
                        size_t *to_merge, struct line **dest)
{
    while (*lo != end_lo && *hi != end_hi && (*to_merge)--)
    {
        if (compare(*lo - 1, *hi - 1) <= 0)
            *--(*dest) = *--(*lo);
        else
            *--(*dest) = *--(*hi);
    }
}

static void merge_lines_to_output(struct line **lo, struct line **hi,
                                  struct line *end_lo, struct line *end_hi,
                                  size_t *to_merge, FILE *tfp, char const *temp_output)
{
    while (*lo != end_lo && *hi != end_hi && (*to_merge)--)
    {
        if (compare(*lo - 1, *hi - 1) <= 0)
            write_unique(--(*lo), tfp, temp_output);
        else
            write_unique(--(*hi), tfp, temp_output);
    }
}

static void copy_remaining_lo(struct line **lo, struct line *end_lo,
                              size_t *to_merge, struct line **dest)
{
    while (*lo != end_lo && (*to_merge)--)
        *--(*dest) = *--(*lo);
}

static void copy_remaining_hi(struct line **hi, struct line *end_hi,
                              size_t *to_merge, struct line **dest)
{
    while (*hi != end_hi && (*to_merge)--)
        *--(*dest) = *--(*hi);
}

static void copy_remaining_lo_to_output(struct line **lo, struct line *end_lo,
                                        size_t *to_merge, FILE *tfp, char const *temp_output)
{
    while (*lo != end_lo && (*to_merge)--)
        write_unique(--(*lo), tfp, temp_output);
}

static void copy_remaining_hi_to_output(struct line **hi, struct line *end_hi,
                                        size_t *to_merge, FILE *tfp, char const *temp_output)
{
    while (*hi != end_hi && (*to_merge)--)
        write_unique(--(*hi), tfp, temp_output);
}

static void merge_to_buffer(struct merge_node *restrict node, size_t *to_merge)
{
    struct line *dest = *node->dest;
    merge_lines(&node->lo, &node->hi, node->end_lo, node->end_hi, to_merge, &dest);
    *node->dest = dest;
}

static void merge_to_output(struct merge_node *restrict node, size_t *to_merge,
                           FILE *tfp, char const *temp_output)
{
    merge_lines_to_output(&node->lo, &node->hi, node->end_lo, node->end_hi, 
                         to_merge, tfp, temp_output);
}

static void copy_remaining_to_buffer(struct merge_node *restrict node, 
                                     size_t merged_lo, size_t merged_hi, size_t *to_merge)
{
    struct line *dest = *node->dest;
    if (node->nhi == merged_hi)
        copy_remaining_lo(&node->lo, node->end_lo, to_merge, &dest);
    else if (node->nlo == merged_lo)
        copy_remaining_hi(&node->hi, node->end_hi, to_merge, &dest);
    *node->dest = dest;
}

static void copy_remaining_to_output(struct merge_node *restrict node,
                                     size_t merged_lo, size_t merged_hi, size_t *to_merge,
                                     FILE *tfp, char const *temp_output)
{
    if (node->nhi == merged_hi)
        copy_remaining_lo_to_output(&node->lo, node->end_lo, to_merge, tfp, temp_output);
    else if (node->nlo == merged_lo)
        copy_remaining_hi_to_output(&node->hi, node->end_hi, to_merge, tfp, temp_output);
}

static void mergelines_node(struct merge_node *restrict node, size_t total_lines,
                           FILE *tfp, char const *temp_output)
{
    struct line *lo_orig = node->lo;
    struct line *hi_orig = node->hi;
    size_t to_merge = MAX_MERGE(total_lines, node->level);
    size_t merged_lo;
    size_t merged_hi;

    if (node->level > MERGE_ROOT)
    {
        merge_to_buffer(node, &to_merge);
        merged_lo = lo_orig - node->lo;
        merged_hi = hi_orig - node->hi;
        copy_remaining_to_buffer(node, merged_lo, merged_hi, &to_merge);
    }
    else
    {
        merge_to_output(node, &to_merge, tfp, temp_output);
        merged_lo = lo_orig - node->lo;
        merged_hi = hi_orig - node->hi;
        copy_remaining_to_output(node, merged_lo, merged_hi, &to_merge, tfp, temp_output);
    }

    merged_lo = lo_orig - node->lo;
    merged_hi = hi_orig - node->hi;
    node->nlo -= merged_lo;
    node->nhi -= merged_hi;
}

/* Into QUEUE, insert NODE if it is not already queued, and if one of
   NODE's children has available lines and the other either has
   available lines or has exhausted its lines.  */

static void
queue_check_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (node->queued)
    return;

  bool lo_avail = (node->lo - node->end_lo) != 0;
  bool hi_avail = (node->hi - node->end_hi) != 0;
  
  bool should_insert = false;
  
  if (lo_avail && !node->nhi)
    should_insert = true;
  else if (hi_avail && !node->nlo)
    should_insert = true;
  else if (lo_avail && hi_avail)
    should_insert = true;
    
  if (should_insert)
    queue_insert (queue, node);
}

/* Into QUEUE, insert NODE's parent if the parent can now be worked on.  */

static void
queue_check_insert_parent (struct merge_node_queue *queue,
                           struct merge_node *node)
{
  if (node->level > MERGE_ROOT)
    {
      lock_node (node->parent);
      queue_check_insert (queue, node->parent);
      unlock_node (node->parent);
    }
  else if (node->nlo + node->nhi == 0)
    {
      queue_insert (queue, node->parent);
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
  while (true)
    {
      struct merge_node *node = queue_pop (queue);

      if (node->level == MERGE_END)
        {
          reinsert_and_unlock (queue, node);
          break;
        }
      
      process_merge_node (queue, node, total_lines, tfp, temp_output);
    }
}

static void
reinsert_and_unlock (struct merge_node_queue *queue, struct merge_node *node)
{
  unlock_node (node);
  queue_insert (queue, node);
}

static void
process_merge_node (struct merge_node_queue *queue, struct merge_node *node,
                    size_t total_lines, FILE *tfp, char const *temp_output)
{
  mergelines_node (node, total_lines, tfp, temp_output);
  queue_check_insert (queue, node);
  queue_check_insert_parent (queue, node);
  unlock_node (node);
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
  struct thread_args const *args = data;
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

static void *sortlines_thread(void *data)
{
    struct thread_args *args = data;
    sortlines(args->lines, args->nthreads, args->total_lines,
              args->node, args->queue, args->tfp, args->temp_output);
    return nullptr;
}

static void sort_single_partition(struct line *lines, size_t count, 
                                   struct line *temp, bool use_half_temp)
{
    if (count > 1)
    {
        struct line *temp_buffer = use_half_temp ? temp - count / 2 : temp;
        sequential_sort(lines, count, temp_buffer, false);
    }
}

static void update_merge_node(struct merge_node *node, struct line *lines,
                               size_t nlo, size_t nhi)
{
    node->lo = lines;
    node->hi = lines - nlo;
    node->end_lo = lines - nlo;
    node->end_hi = lines - nlo - nhi;
}

static void sort_sequential(struct line *lines, size_t total_lines,
                             struct merge_node *node, struct merge_node_queue *queue,
                             FILE *tfp, char const *temp_output)
{
    size_t nlo = node->nlo;
    size_t nhi = node->nhi;
    struct line *temp = lines - total_lines;
    
    sort_single_partition(lines - nlo, nhi, temp, true);
    sort_single_partition(lines, nlo, temp, false);
    
    update_merge_node(node, lines, nlo, nhi);
    queue_insert(queue, node);
    merge_loop(queue, total_lines, tfp, temp_output);
}

static bool should_use_parallel(size_t nthreads, size_t nlines)
{
    return nthreads > 1 && SUBTHREAD_LINES_HEURISTIC <= nlines;
}

static void sort_parallel(struct line *lines, size_t nthreads, size_t total_lines,
                           struct merge_node *node, struct merge_node_queue *queue,
                           FILE *tfp, char const *temp_output)
{
    size_t lo_threads = nthreads / 2;
    size_t hi_threads = nthreads - lo_threads;
    pthread_t thread;
    struct thread_args args = {lines, lo_threads, total_lines,
                               node->lo_child, queue, tfp, temp_output};
    
    if (pthread_create(&thread, nullptr, sortlines_thread, &args) == 0)
    {
        sortlines(lines - node->nlo, hi_threads, total_lines,
                  node->hi_child, queue, tfp, temp_output);
        pthread_join(thread, nullptr);
    }
    else
    {
        sort_sequential(lines, total_lines, node, queue, tfp, temp_output);
    }
}

static void sortlines(struct line *restrict lines, size_t nthreads,
                      size_t total_lines, struct merge_node *node,
                      struct merge_node_queue *queue, FILE *tfp, char const *temp_output)
{
    size_t nlines = node->nlo + node->nhi;
    
    if (should_use_parallel(nthreads, nlines))
    {
        sort_parallel(lines, nthreads, total_lines, node, queue, tfp, temp_output);
    }
    else
    {
        sort_sequential(lines, total_lines, node, queue, tfp, temp_output);
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

static bool is_same_as_stdin(const char *filename) {
    return STREQ(filename, "-");
}

static bool is_same_as_output(const char *filename, const char *outfile) {
    return outfile && STREQ(outfile, filename);
}

static int get_file_stat(const char *filename, bool is_stdin, struct stat *instat) {
    if (is_stdin) {
        return fstat(STDIN_FILENO, instat);
    }
    return stat(filename, instat);
}

static bool check_same_inode(const char *filename, bool is_stdin, struct stat *outst) {
    struct stat instat;
    if (get_file_stat(filename, is_stdin, &instat) != 0) {
        return false;
    }
    return psame_inode(&instat, outst);
}

static bool is_same_file(const char *filename, const char *outfile, bool is_stdin) {
    if (is_same_as_output(filename, outfile) && !is_stdin) {
        return true;
    }
    
    struct stat *outst = get_outstatus();
    if (!outst) {
        return false;
    }
    
    return check_same_inode(filename, is_stdin, outst);
}

static struct tempnode* create_temp_copy(struct sortfile *file) {
    FILE *tftp;
    struct tempnode *tempcopy = create_temp(&tftp);
    mergefiles(file, 0, 1, tftp, tempcopy->name);
    return tempcopy;
}

static void replace_with_temp(struct sortfile *file, struct tempnode **tempcopy) {
    if (!*tempcopy) {
        *tempcopy = create_temp_copy(file);
    }
    file->name = (*tempcopy)->name;
    file->temp = *tempcopy;
}

static void avoid_trashing_input(struct sortfile *files, size_t ntemps,
                                size_t nfiles, char const *outfile) {
    struct tempnode *tempcopy = nullptr;
    
    for (size_t i = ntemps; i < nfiles; i++) {
        bool is_stdin = is_same_as_stdin(files[i].name);
        bool same = is_same_file(files[i].name, outfile, is_stdin);
        
        if (same) {
            replace_with_temp(&files[i], &tempcopy);
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
check_inputs (char *const *files, size_t nfiles)
{
  for (size_t i = 0; i < nfiles; i++)
    {
      if (STREQ (files[i], "-"))
        continue;

      if (euidaccess (files[i], R_OK) != 0)
        sort_die (_("cannot read"), files[i]);
    }
}

/* Ensure a specified output file can be created or written to,
   and point stdout to it.  Do not truncate the file.
   Exit with a diagnostic on failure.  */

static void
check_output (char const *outfile)
{
  if (!outfile)
    return;
    
  int oflags = O_WRONLY | O_BINARY | O_CLOEXEC | O_CREAT;
  int outfd = open (outfile, oflags, MODE_RW_UGO);
  if (outfd < 0)
    sort_die (_("open failed"), outfile);
  move_fd (outfd, STDOUT_FILENO);
}

/* Merge the input FILES.  NTEMPS is the number of files at the
   start of FILES that are temporary; it is zero at the top level.
   NFILES is the total number of files.  Put the output in
   OUTPUT_FILE; a null OUTPUT_FILE stands for standard output.  */

static size_t perform_full_merges(struct sortfile *files, size_t ntemps, size_t nfiles, size_t *in)
{
    size_t out = 0;
    *in = 0;
    
    while (nmerge <= nfiles - *in)
    {
        FILE *tfp;
        struct tempnode *temp = create_temp(&tfp);
        size_t num_merged = mergefiles(&files[*in], MIN(ntemps, nmerge),
                                      nmerge, tfp, temp->name);
        ntemps -= MIN(ntemps, num_merged);
        files[out].name = temp->name;
        files[out].temp = temp;
        *in += num_merged;
        out++;
    }
    
    return out;
}

static size_t perform_short_merge(struct sortfile *files, size_t ntemps, size_t in, 
                                 size_t out, size_t nshortmerge)
{
    FILE *tfp;
    struct tempnode *temp = create_temp(&tfp);
    size_t num_merged = mergefiles(&files[in], MIN(ntemps, nshortmerge),
                                  nshortmerge, tfp, temp->name);
    files[out].name = temp->name;
    files[out].temp = temp;
    return num_merged;
}

static void handle_remaining_files(struct sortfile *files, size_t ntemps, size_t nfiles,
                                  size_t in, size_t out, size_t *ntemps_out, size_t *nfiles_out)
{
    size_t remainder = nfiles - in;
    size_t cheap_slots = nmerge - out % nmerge;
    
    if (cheap_slots < remainder)
    {
        size_t nshortmerge = remainder - cheap_slots + 1;
        size_t num_merged = perform_short_merge(files, ntemps, in, out, nshortmerge);
        ntemps -= MIN(ntemps, num_merged);
        out++;
        in += num_merged;
    }
    
    memmove(&files[out], &files[in], (nfiles - in) * sizeof *files);
    *ntemps_out = ntemps + out;
    *nfiles_out = nfiles - in + out;
}

static int try_direct_merge(struct sortfile *files, size_t ntemps, size_t nfiles,
                           char const *output_file, FILE **fps, size_t nopened)
{
    if (nopened == nfiles)
    {
        FILE *ofp = stream_open(output_file, "w");
        if (ofp)
        {
            mergefps(files, ntemps, nfiles, ofp, output_file, fps);
            return 1;
        }
        if (errno != EMFILE || nopened <= 2)
            sort_die(_("open failed"), output_file);
    }
    else if (nopened <= 2)
    {
        sort_die(_("open failed"), files[nopened].name);
    }
    return 0;
}

static struct tempnode* recover_file_descriptor(FILE **fps, struct sortfile *files, 
                                               size_t *nopened, FILE **tfp)
{
    struct tempnode *temp;
    do
    {
        (*nopened)--;
        xfclose(fps[*nopened], files[*nopened].name);
        temp = maybe_create_temp(tfp, !(*nopened <= 2));
    }
    while (!temp);
    return temp;
}

static void merge_to_temporary(struct sortfile *files, size_t *ntemps, size_t *nfiles,
                              FILE **fps, size_t nopened)
{
    FILE *tfp;
    struct tempnode *temp = recover_file_descriptor(fps, files, &nopened, &tfp);
    
    mergefps(&files[0], MIN(*ntemps, nopened), nopened, tfp, temp->name, fps);
    *ntemps -= MIN(*ntemps, nopened);
    files[0].name = temp->name;
    files[0].temp = temp;
    
    memmove(&files[1], &files[nopened], (*nfiles - nopened) * sizeof *files);
    (*ntemps)++;
    *nfiles -= nopened - 1;
}

static void merge(struct sortfile *files, size_t ntemps, size_t nfiles,
                 char const *output_file)
{
    while (nmerge < nfiles)
    {
        size_t in;
        size_t out = perform_full_merges(files, ntemps, nfiles, &in);
        handle_remaining_files(files, ntemps, nfiles, in, out, &ntemps, &nfiles);
    }
    
    avoid_trashing_input(files, ntemps, nfiles, output_file);
    
    while (1)
    {
        FILE **fps;
        size_t nopened = open_input_files(files, nfiles, &fps);
        
        if (try_direct_merge(files, ntemps, nfiles, output_file, fps, nopened))
            break;
            
        merge_to_temporary(files, &ntemps, &nfiles, fps, nopened);
    }
}

/* Sort NFILES FILES onto OUTPUT_FILE.  Use at most NTHREADS threads.  */

static size_t calculate_bytes_per_line(size_t nthreads)
{
    if (nthreads > 1)
    {
        size_t tmp = 1;
        size_t mult = 1;
        while (tmp < nthreads)
        {
            tmp *= 2;
            mult++;
        }
        return mult * sizeof(struct line);
    }
    return sizeof(struct line) * 3 / 2;
}

static bool should_concatenate_next_file(struct buffer *buf, size_t nfiles, size_t bytes_per_line)
{
    return buf->eof && nfiles &&
           (bytes_per_line + 1 < (buf->alloc - buf->used - bytes_per_line * buf->nlines));
}

static bool is_final_output(struct buffer *buf, size_t nfiles, size_t ntemps)
{
    return buf->eof && !nfiles && !ntemps && !buf->left;
}

static FILE *open_output_file(const char *file, const char *output_file, 
                              char const **temp_output, bool *output_file_created)
{
    FILE *tfp = xfopen(output_file, "w");
    *temp_output = output_file;
    *output_file_created = true;
    return tfp;
}

static FILE *create_temp_output(size_t *ntemps, char const **temp_output)
{
    FILE *tfp;
    (*ntemps)++;
    *temp_output = create_temp(&tfp)->name;
    return tfp;
}

static void process_sorted_lines(struct line *line, struct buffer *buf, 
                                size_t nthreads, FILE *tfp, const char *temp_output)
{
    if (1 < buf->nlines)
    {
        struct merge_node_queue queue;
        queue_init(&queue, nthreads);
        struct merge_node *merge_tree = merge_tree_init(nthreads, buf->nlines, line);
        
        sortlines(line, nthreads, buf->nlines, merge_tree + 1, &queue, tfp, temp_output);
        
        merge_tree_destroy(nthreads, merge_tree);
        queue_destroy(&queue);
    }
    else
    {
        write_unique(line - 1, tfp, temp_output);
    }
}

static void merge_temp_files(size_t ntemps, const char *output_file)
{
    struct tempnode *node = temphead;
    struct sortfile *tempfiles = xnmalloc(ntemps, sizeof *tempfiles);
    
    for (size_t i = 0; node; i++)
    {
        tempfiles[i].name = node->name;
        tempfiles[i].temp = node;
        node = node->next;
    }
    
    merge(tempfiles, ntemps, ntemps, output_file);
    free(tempfiles);
}

static bool process_buffer_chunk(struct buffer *buf, FILE *fp, const char *file,
                                 size_t nfiles, size_t ntemps, size_t nthreads,
                                 const char *output_file, bool *output_file_created,
                                 size_t *ntemps_ptr, size_t bytes_per_line)
{
    struct line *line;
    
    if (should_concatenate_next_file(buf, nfiles, bytes_per_line))
    {
        buf->left = buf->used;
        return false;
    }
    
    saved_line.text = nullptr;
    line = buffer_linelim(buf);
    
    const char *temp_output;
    FILE *tfp;
    
    if (is_final_output(buf, nfiles, ntemps))
    {
        xfclose(fp, file);
        tfp = open_output_file(file, output_file, &temp_output, output_file_created);
    }
    else
    {
        tfp = create_temp_output(ntemps_ptr, &temp_output);
    }
    
    process_sorted_lines(line, buf, nthreads, tfp, temp_output);
    xfclose(tfp, temp_output);
    
    return *output_file_created;
}

static void sort(char *const *files, size_t nfiles, char const *output_file, size_t nthreads)
{
    struct buffer buf;
    size_t ntemps = 0;
    bool output_file_created = false;
    
    buf.alloc = 0;
    
    while (nfiles)
    {
        char const *file = *files;
        FILE *fp = xfopen(file, "r");
        
        size_t bytes_per_line = calculate_bytes_per_line(nthreads);
        
        if (!buf.alloc)
            initbuf(&buf, bytes_per_line,
                   sort_buffer_size(&fp, 1, files, nfiles, bytes_per_line));
        
        buf.eof = false;
        files++;
        nfiles--;
        
        while (fillbuf(&buf, fp, file))
        {
            if (process_buffer_chunk(&buf, fp, file, nfiles, ntemps, nthreads,
                                    output_file, &output_file_created, &ntemps, bytes_per_line))
                goto finish;
        }
        
        xfclose(fp, file);
    }
    
finish:
    free(buf.buf);
    
    if (!output_file_created)
        merge_temp_files(ntemps, output_file);
    
    reap_all();
}

/* Insert a malloc'd copy of key KEY_ARG at the end of the key list.  */

static void
insertkey (struct keyfield *key_arg)
{
  struct keyfield **p = &keylist;
  struct keyfield *key = xmemdup (key_arg, sizeof *key);

  while (*p)
    p = &(*p)->next;
    
  *p = key;
  key->next = nullptr;
}

/* Report a bad field specification SPEC, with extra info MSGID.  */

static void
badfieldspec (char const *spec, char const *msgid)
{
  error (SORT_FAILURE, 0, _("%s: invalid field specification %s"),
         _(msgid), quote (spec));
}

/* Report incompatible options.  */

static void
incompatible_options (char const *opts)
{
  error (SORT_FAILURE, 0, _("options '-%s' are incompatible"), opts);
}

/* Check compatibility of ordering options.  */

static bool is_multiple_sort_type(struct keyfield *key)
{
    int sort_type_count = key->numeric + key->general_numeric + key->human_numeric
                         + key->month + (key->version | key->random | !!key->ignore);
    return sort_type_count > 1;
}

static void clear_uninterested_flags(struct keyfield *key)
{
    key->skipsblanks = false;
    key->skipeblanks = false;
    key->reverse = false;
}

static void check_key_compatibility(struct keyfield *key)
{
    char opts[sizeof short_options];
    clear_uninterested_flags(key);
    key_to_opts(key, opts);
    incompatible_options(opts);
}

static void check_ordering_compatibility(void)
{
    struct keyfield *key;
    
    for (key = keylist; key; key = key->next)
    {
        if (is_multiple_sort_type(key))
        {
            check_key_compatibility(key);
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
  strtol_error result = xstrtoumax (string, &suffix, 10, &n, "");

  if (result == LONGINT_INVALID)
    {
      if (msgid)
        error (SORT_FAILURE, 0, _("%s: invalid count at start of %s"),
               _(msgid), quote (string));
      return nullptr;
    }

  bool is_overflow = (result == LONGINT_OVERFLOW) || 
                     (result == (LONGINT_OVERFLOW | LONGINT_INVALID_SUFFIX_CHAR));
  
  if (is_overflow)
    {
      *val = SIZE_MAX;
    }
  else
    {
      *val = (n == (size_t)n) ? n : SIZE_MAX;
    }

  return suffix;
}

/* Handle interrupts and hangups. */

static void
sighandler (int sig)
{
  if (! SA_NOCLDSTOP)
    signal (sig, SIG_IGN);

  cleanup ();

  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set the ordering options for KEY specified in S.
   Return the address of the first character in S that
   is not a valid ordering option.
   BLANKTYPE is the kind of blanks that 'b' should skip. */

static void set_blank_options(struct keyfield *key, enum blanktype blanktype)
{
    if (blanktype == bl_start || blanktype == bl_both)
        key->skipsblanks = true;
    if (blanktype == bl_end || blanktype == bl_both)
        key->skipeblanks = true;
}

static void set_ignore_option(struct keyfield *key, char option)
{
    if (option == 'd')
        key->ignore = nondictionary;
    else if (option == 'i' && !key->ignore)
        key->ignore = nonprinting;
}

static void set_key_option(struct keyfield *key, char option)
{
    switch (option)
    {
    case 'f':
        key->translate = fold_toupper;
        break;
    case 'g':
        key->general_numeric = true;
        break;
    case 'h':
        key->human_numeric = true;
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
    }
}

static char *
set_ordering (char const *s, struct keyfield *key, enum blanktype blanktype)
{
    while (*s)
    {
        if (*s == 'b')
            set_blank_options(key, blanktype);
        else if (*s == 'd' || *s == 'i')
            set_ignore_option(key, *s);
        else if (*s == 'f' || *s == 'g' || *s == 'h' || *s == 'M' || 
                 *s == 'n' || *s == 'R' || *s == 'r' || *s == 'V')
            set_key_option(key, *s);
        else
            return (char *) s;
        ++s;
    }
    return (char *) s;
}

/* Initialize KEY.  */

static struct keyfield *
key_init (struct keyfield *key)
{
  memset (key, 0, sizeof *key);
  key->eword = SIZE_MAX;
  return key;
}

int main(int argc, char **argv) {
    struct keyfield *key;
    struct keyfield key_buf;
    struct keyfield gkey;
    bool gkey_only = false;
    char const *s;
    int c = 0;
    char checkonly = 0;
    bool mergeonly = false;
    char *random_source = nullptr;
    bool need_random = false;
    size_t nthreads = 0;
    size_t nfiles = 0;
    bool posixly_correct = (getenv("POSIXLY_CORRECT") != nullptr);
    int posix_ver = posix2_version();
    bool traditional_usage = !(200112 <= posix_ver && posix_ver < 200809);
    char **files;
    char *files_from = nullptr;
    struct Tokens tok;
    char const *outfile = nullptr;
    bool locale_ok;

    initialize_main(&argc, &argv);
    set_program_name(argv[0]);
    locale_ok = !!setlocale(LC_ALL, "");
    bindtextdomain(PACKAGE, LOCALEDIR);
    textdomain(PACKAGE);

    initialize_exit_failure(SORT_FAILURE);

    hard_LC_COLLATE = hard_locale(LC_COLLATE);
#if HAVE_NL_LANGINFO
    hard_LC_TIME = hard_locale(LC_TIME);
#endif

    initialize_locale_settings();
    have_read_stdin = false;
    inittables();
    setup_signal_handlers();
    signal(SIGCHLD, SIG_DFL);
    atexit(exit_cleanup);

    key_init(&gkey);
    gkey.sword = SIZE_MAX;

    files = xnmalloc(argc, sizeof *files);

    while (true) {
        if (should_parse_file_operand(c, posixly_correct, nfiles, traditional_usage, 
                                     checkonly, optind, argc, argv)) {
            if (argc <= optind)
                break;
            files[nfiles++] = argv[optind++];
        } else if ((c = getopt_long(argc, argv, short_options, long_options, &oi)) == -1) {
            if (argc <= optind)
                break;
            files[nfiles++] = argv[optind++];
        } else {
            handle_option(c, &optarg, &key, &key_buf, &gkey, &checkonly, &mergeonly,
                        &random_source, &nthreads, &nfiles, files, &files_from,
                        &outfile, &traditional_usage, &posixly_correct, 
                        argc, argv, &optind, &oi);
        }
    }

    process_files_from_input(files_from, &files, &nfiles, &tok);
    inherit_global_options(keylist, &gkey, &need_random);

    if (!keylist && !default_key_compare(&gkey)) {
        gkey_only = true;
        insertkey(&gkey);
        need_random |= gkey.random;
    }

    check_ordering_compatibility();
    handle_debug_mode(debug, checkonly, outfile, locale_ok, &gkey, gkey_only);
    
    reverse = gkey.reverse;

    if (need_random)
        random_md5_state_init(random_source);

    setup_temp_directories();
    setup_default_input(&nfiles, &files);
    validate_sort_size();

    if (checkonly) {
        validate_check_mode(nfiles, files, checkonly, outfile);
        exit(check(files[0], checkonly) ? EXIT_SUCCESS : SORT_OUT_OF_ORDER);
    }

    check_inputs(files, nfiles);
    check_output(outfile);

    if (mergeonly) {
        perform_merge(files, nfiles, outfile);
    } else {
        setup_threads(&nthreads);
        sort(files, nfiles, outfile, nthreads);
    }

    if (have_read_stdin && fclose(stdin) == EOF)
        sort_die(_("close failed"), "-");

    main_exit(EXIT_SUCCESS);
}

void initialize_locale_settings(void) {
    struct lconv const *locale = localeconv();
    
    decimal_point = locale->decimal_point[0];
    if (!decimal_point || locale->decimal_point[1])
        decimal_point = '.';

    thousands_sep = locale->thousands_sep[0];
    if (thousands_sep && locale->thousands_sep[1])
        thousands_sep_ignored = true;
    if (!thousands_sep || locale->thousands_sep[1])
        thousands_sep = NON_CHAR;
}

void setup_signal_handlers(void) {
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
    enum { nsigs = ARRAY_CARDINALITY(sig) };

#if SA_NOCLDSTOP
    struct sigaction act;
    sigemptyset(&caught_signals);
    
    for (size_t i = 0; i < nsigs; i++) {
        sigaction(sig[i], nullptr, &act);
        if (act.sa_handler != SIG_IGN)
            sigaddset(&caught_signals, sig[i]);
    }

    act.sa_handler = sighandler;
    act.sa_mask = caught_signals;
    act.sa_flags = 0;

    for (size_t i = 0; i < nsigs; i++)
        if (sigismember(&caught_signals, sig[i]))
            sigaction(sig[i], &act, nullptr);
#else
    for (size_t i = 0; i < nsigs; i++)
        if (signal(sig[i], SIG_IGN) != SIG_IGN) {
            signal(sig[i], sighandler);
            siginterrupt(sig[i], 1);
        }
#endif
}

bool should_parse_file_operand(int c, bool posixly_correct, size_t nfiles,
                              bool traditional_usage, char checkonly,
                              int optind, int argc, char **argv) {
    if (c == -1)
        return true;
    
    if (!posixly_correct || nfiles == 0)
        return false;
        
    if (!traditional_usage || checkonly)
        return true;
        
    if (optind == argc)
        return true;
        
    return !(argv[optind][0] == '-' && argv[optind][1] == 'o' 
            && (argv[optind][2] || optind + 1 != argc));
}

void handle_option(int c, char **optarg_ptr, struct keyfield **key, 
                  struct keyfield *key_buf, struct keyfield *gkey,
                  char *checkonly, bool *mergeonly, char **random_source,
                  size_t *nthreads, size_t *nfiles, char **files,
                  char **files_from, char const **outfile,
                  bool *traditional_usage, bool *posixly_correct,
                  int argc, char **argv, int *optind, int *oi) {
    char *optarg = *optarg_ptr;
    
    switch (c) {
        case 1:
            handle_positional_arg(optarg, key, key_buf, nfiles, files,
                                traditional_usage, posixly_correct, 
                                optind, argc, argv);
            break;
        case SORT_OPTION:
            c = XARGMATCH("--sort", optarg, sort_args, sort_types);
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
            handle_ordering_option(c, gkey);
            break;
        case CHECK_OPTION:
            c = optarg ? XARGMATCH("--check", optarg, check_args, check_types) : 'c';
        case 'c':
        case 'C':
            handle_check_option(c, checkonly);
            break;
        case COMPRESS_PROGRAM_OPTION:
            handle_compress_program(optarg);
            break;
        case DEBUG_PROGRAM_OPTION:
            debug = true;
            break;
        case FILES0_FROM_OPTION:
            *files_from = optarg;
            break;
        case 'k':
            handle_key_option(optarg, key_buf);
            break;
        case 'm':
            *mergeonly = true;
            break;
        case NMERGE_OPTION:
            specify_nmerge(*oi, c, optarg);
            break;
        case 'o':
            handle_output_file(optarg, outfile);
            break;
        case RANDOM_SOURCE_OPTION:
            handle_random_source(optarg, random_source);
            break;
        case 's':
            stable = true;
            break;
        case 'S':
            specify_sort_size(*oi, c, optarg);
            break;
        case 't':
            handle_tab_option(optarg);
            break;
        case 'T':
            add_temp_dir(optarg);
            break;
        case PARALLEL_OPTION:
            *nthreads = specify_nthreads(*oi, c, optarg);
            break;
        case 'u':
            unique = true;
            break;
        case 'y':
            handle_y_option(optarg, argv, *optind);
            break;
        case 'z':
            eolchar = 0;
            break;
        case_GETOPT_HELP_CHAR;
        case_GETOPT_VERSION_CHAR(PROGRAM_NAME, AUTHORS);
        default:
            usage(SORT_FAILURE);
    }
}

void handle_positional_arg(char *optarg, struct keyfield **key,
                          struct keyfield *key_buf, size_t *nfiles,
                          char **files, bool *traditional_usage,
                          bool *posixly_correct, int *optind,
                          int argc, char **argv) {
    *key = nullptr;
    
    if (optarg[0] == '+') {
        bool minus_pos_usage = (*optind != argc && argv[*optind][0] == '-'
                              && c_isdigit(argv[*optind][1]));
        *traditional_usage |= minus_pos_usage && !*posixly_correct;
        
        if (*traditional_usage) {
            process_traditional_key(optarg, key, key_buf, minus_pos_usage, 
                                  optind, argv);
        }
    }
    
    if (!*key)
        files[(*nfiles)++] = optarg;
}

void process_traditional_key(char *optarg, struct keyfield **key,
                            struct keyfield *key_buf, bool minus_pos_usage,
                            int *optind, char **argv) {
    char const *s;
    *key = key_init(key_buf);
    
    s = parse_field_count(optarg + 1, &(*key)->sword, nullptr);
    if (s && *s == '.')
        s = parse_field_count(s + 1, &(*key)->schar, nullptr);
    
    if (!((*key)->sword || (*key)->schar))
        (*key)->sword = SIZE_MAX;
    
    if (!s || *set_ordering(s, *key, bl_start)) {
        *key = nullptr;
    } else {
        if (minus_pos_usage) {
            parse_minus_pos_usage(argv[(*optind)++], *key);
        }
        (*key)->traditional_used = true;
        insertkey(*key);
    }
}

void parse_minus_pos_usage(char const *optarg1, struct keyfield *key) {
    char const *s = parse_field_count(optarg1 + 1, &key->eword,
                                     N_("invalid number after '-'"));
    if (*s == '.')
        s = parse_field_count(s + 1, &key->echar,
                            N_("invalid number after '.'"));
    
    if (!key->echar && key->eword)
        key->eword--;
    
    if (*set_ordering(s, key, bl_end))
        badfieldspec(optarg1, N_("stray character in field spec"));
}

void handle_ordering_option(int c, struct keyfield *gkey) {
    char str[2];
    str[0] = c;
    str[1] = '\0';
    set_ordering(str, gkey, bl_both);
}

void handle_check_option(int c, char *checkonly) {
    if (*checkonly && *checkonly != c)
        incompatible_options("cC");
    *checkonly = c;
}

void handle_compress_program(char *optarg) {
    if (compress_program && !STREQ(compress_program, optarg))
        error(SORT_FAILURE, 0, _("multiple compress programs specified"));
    compress_program = optarg;
}

void handle_key_option(char *optarg, struct keyfield *key_buf) {
    struct keyfield *key = key_init(key_buf);
    char const *s;
    
    s = parse_key_start(optarg, key);
    s = set_ordering(s, key, bl_start);
    
    if (*s != ',') {
        key->eword = SIZE_MAX;
        key->echar = 0;
    } else {
        s = parse_key_end(s + 1, key);
        s = set_ordering(s, key, bl_end);
    }
    
    if (*s)
        badfieldspec(optarg, N_("stray character in field spec"));
    
    insertkey(key);
}

char const *parse_key_start(char const *s, struct keyfield *key) {
    s = parse_field_count(s, &key->sword, N_("invalid number at field start"));
    
    if (!key->sword--)
        badfieldspec(s, N_("field number is zero"));
    
    if (*s == '.') {
        s = parse_field_count(s + 1, &key->schar, N_("invalid number after '.'"));
        if (!key->schar--)
            badfieldspec(s, N_("character offset is zero"));
    }
    
    if (!(key->sword || key->schar))
        key->sword = SIZE_MAX;
    
    return s;
}

char const *parse_key_end(char const *s, struct keyfield *key) {
    s = parse_field_count(s, &key->eword, N_("invalid number after ','"));
    
    if (!key->eword--)
        badfieldspec(s, N_("field number is zero"));
    
    if (*s == '.')
        s = parse_field_count(s + 1, &key->echar, N_("invalid number after '.'"));
    
    return s;
}

void handle_output_file(char *optarg, char const **outfile) {
    if (*outfile && !STREQ(*outfile, optarg))
        error(SORT_FAILURE, 0, _("multiple output files specified"));
    *outfile = optarg;
}

void handle_random_source(char *optarg, char **random_source) {
    if (*random_source && !STREQ(*random_source, optarg))
        error(SORT_FAILURE, 0, _("multiple random sources specified"));
    *random_source = optarg;
}

void handle_tab_option(char *optarg) {
    char newtab = optarg[0];
    
    if (!newtab)
        error(SORT_FAILURE, 0, _("empty tab"));
    
    if (optarg[1]) {
        if (STREQ(optarg, "\\0"))
            newtab = '\0';
        else
            error(SORT_FAILURE, 0, _("multi-character tab %s"), quote(optarg));
    }
    
    if (tab != TAB_DEFAULT && tab != newtab)
        error(SORT_FAILURE, 0, _("incompatible tabs"));
    
    tab = newtab;
}

void handle_y_option(char *optarg, char **argv, int optind) {
    if (optarg == argv[optind - 1]) {
        char const *p;
        for (p = optarg; c_isdigit(*p); p++)
            continue;
        optind -= (*p != '\0');
    }
}

void process_files_from_input(char *files_from, char ***files, 
                             size_t *nfiles, struct Tokens *tok) {
    if (!files_from)
        return;
    
    validate_files_from_usage(*nfiles, *files);
    
    FILE *stream = xfopen(files_from, "r");
    readtokens0_init(tok);
    
    if (!readtokens0(stream, tok))
        error(SORT_FAILURE, 0, _("cannot read file names from %s"),
              quoteaf(files_from));
    xfclose(stream, files_from);
    
    if (tok->n_tok) {
        free(*files);
        *files = tok->tok;
        *nfiles = tok->n_tok;
        validate_file_names(*files, *nfiles, files_from);
    } else {
        error(SORT_FAILURE, 0, _("no input from %s"), quoteaf(files_from));
    }
}

void validate_files_from_usage(size_t nfiles, char **files) {
    if (nfiles) {
        error(0, 0, _("extra operand %s"), quoteaf(files[0]));
        fprintf(stderr, "%s\n", 
               _("file operands cannot be combined with --files0-from"));
        usage(SORT_FAILURE);
    }
}

void validate_file_names(char **files, size_t nfiles, char *files_from) {
    for (size_t i = 0; i < nfiles; i++) {
        if (STREQ(files[i], "-")) {
            error(SORT_FAILURE, 0, 
                 _("when reading file names from standard input, "
                   "no file name of %s allowed"), quoteaf(files[i]));
        } else if (files[i][0] == '\0') {
            unsigned long int file_number = i + 1;
            error(SORT_FAILURE, 0,
                 _("%s:%lu: invalid zero-length file name"),
                 quotef(files_from), file_number);
        }
    }
}

void inherit_global_options(struct keyfield *keylist, 
                           struct keyfield *gkey, bool *need_random) {
    for (struct keyfield *key = keylist; key; key = key->next) {
        if (default_key_compare(key) && !key->reverse) {
            copy_key_options(key, gkey);
        }
        *need_random |= key->random;
    }
}

void copy_key_options(struct keyfield *dest, struct keyfield *src) {
    dest->ignore = src->ignore;
    dest->translate = src->translate;
    dest->skipsblanks = src->skipsblanks;
    dest->skipeblanks = src->skipeblanks;
    dest->month = src->month;
    dest->numeric = src->numeric;
    dest->general_numeric = src->general_numeric;
    dest->human_numeric = src->human_numeric;
    dest->version = src->version;
    dest->random = src->random;
    dest->reverse = src->reverse;
}

void handle_debug_mode(bool debug, char checkonly, char const *outfile,
                      bool locale_ok, struct keyfield *gkey, bool gkey_only) {
    if (!debug)
        return;
    
    validate_debug_options(checkonly, outfile);
    print_locale_info(locale_ok);
    key_warnings(gkey, gkey_only);
}

void validate_debug_options(char checkonly, char const *outfile) {
    if (checkonly || outfile) {
        static char opts[] = "X --debug";
        opts[0] = checkonly ? checkonly : 'o';
        incompatible_options(opts);
    }
}

void print_locale_info(bool locale_ok) {
    if (locale_ok)
        locale_ok = !!setlocale(LC_COLLATE, "");
    
    if (!locale_ok)
        error(0, 0, "%s", _("failed to set locale"));
    
    if (hard_LC_COLLATE)
        error(0, 0, _("text ordering performed using %s sorting rules"),
              quote(setlocale(LC_COLLATE, nullptr)));
    else
        error(0, 0, "%s",
              _("text ordering performed using simple byte comparison"));
}

void setup_temp_directories(void) {
    if (temp_dir_count == 0) {
        char const *tmp_dir = getenv("TMPDIR");
        add_temp_dir(tmp_dir ? tmp_dir : DEFAULT_TMPDIR);
    }
}

void setup_default_input(size_t *nfiles, char ***files) {
    if (*nfiles == 0) {
        *nfiles = 1;
        free(*files);
        *files = xmalloc(sizeof **files);
        **files = (char *)"-";
    }
}

void validate_sort_size(void) {
    if (0 < sort_size)
        sort_size = MAX(sort_size, MIN_SORT_SIZE);
}

void validate_check_mode(size_t nfiles, char **files, char checkonly, 
                        char const *outfile) {
    if (nfiles > 1)
        error(SORT_FAILURE, 0, _("extra operand %s not allowed with -%c"),
              quoteaf(files[1]), checkonly);
    
    if (outfile) {
        static char opts[] = {0, 'o', 0};
        opts[0] = checkonly;
        incompatible_options(opts);
    }
}

void perform_merge(char **files, size_t nfiles, char const *outfile) {
    struct sortfile *sortfiles = xcalloc(nfiles, sizeof *sortfiles);
    
    for (size_t i = 0; i < nfiles; ++i)
        sortfiles[i].name = files[i];
    
    merge(sortfiles, 0, nfiles, outfile);
}

void setup_threads(size_t *nthreads) {
    if (!*nthreads) {
        unsigned long int np = num_processors(NPROC_CURRENT_OVERRIDABLE);
        *nthreads = MIN(np, DEFAULT_MAX_THREADS);
    }
    
    size_t nthreads_max = SIZE_MAX / (2 * sizeof(struct merge_node));
    *nthreads = MIN(*nthreads, nthreads_max);
}
