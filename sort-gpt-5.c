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

static size_t
cstr_len (char const *s)
{
  char const *p = s;
  while (*p)
    p++;
  return (size_t) (p - s);
}

static void
safe_write_all (int fd, char const *buf, size_t len)
{
  while (len > 0)
    {
      ssize_t w = write (fd, buf, len);
      if (w <= 0)
        break;
      buf += (size_t) w;
      len -= (size_t) w;
    }
}

static _Noreturn void
async_safe_die (int errnum, char const *errstr)
{
  safe_write_all (STDERR_FILENO, errstr, cstr_len (errstr));

  if (errnum)
    {
      char errbuf[INT_BUFSIZE_BOUND (errnum)];
      char *p = inttostr (errnum, errbuf);
      static char const prefix[] = ": errno ";
      safe_write_all (STDERR_FILENO, prefix, sizeof prefix - 1);
      safe_write_all (STDERR_FILENO, p, cstr_len (p));
    }

  static char const nl[] = "\n";
  safe_write_all (STDERR_FILENO, nl, sizeof nl - 1);

  _exit (SORT_FAILURE);
}

/* Report MESSAGE for FILE, then clean up and exit.
   If FILE is null, it represents standard output.  */

static void
sort_die(char const *message, char const *file)
{
  int saved_errno = errno;
  char const *target = file ? file : _("standard output");
  char const *quoted = quotef(target);
  if (!message)
    message = "";
  if (!quoted)
    quoted = target;
  error(SORT_FAILURE, saved_errno, "%s: %s", message, quoted);
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      emit_try_help ();
      exit (status);
    }

  printf (_("Usage: %s [OPTION]... [FILE]...\n  or:  %s [OPTION]... --files0-from=F\n"),
          program_name, program_name);
  fputs (_("Write sorted concatenation of all FILE(s) to standard output.\n"), stdout);

  emit_stdin_note ();
  emit_mandatory_arg_note ();

  {
    static const char *const sections[] = {
      _("Ordering options:\n\n"),
      _("  -b, --ignore-leading-blanks  ignore leading blanks\n"
        "  -d, --dictionary-order      consider only blanks and alphanumeric characters\n"
        "  -f, --ignore-case           fold lower case to upper case characters\n"),
      _("  -g, --general-numeric-sort  compare according to general numerical value\n"
        "  -i, --ignore-nonprinting    consider only printable characters\n"
        "  -M, --month-sort            compare (unknown) < 'JAN' < ... < 'DEC'\n"),
      _("  -h, --human-numeric-sort    compare human readable numbers (e.g., 2K 1G)\n"),
      _("  -n, --numeric-sort          compare according to string numerical value;\n"
        "                                see full documentation for supported strings\n"),
      _("  -R, --random-sort           shuffle, but group identical keys.  See shuf(1)\n"
        "      --random-source=FILE    get random bytes from FILE\n"
        "  -r, --reverse               reverse the result of comparisons\n"),
      _("      --sort=WORD             sort according to WORD:\n"
        "                                general-numeric -g, human-numeric -h, month -M,\n"
        "                                numeric -n, random -R, version -V\n"
        "  -V, --version-sort          natural sort of (version) numbers within text\n\n"),
      _("Other options:\n\n"),
      _("      --batch-size=NMERGE   merge at most NMERGE inputs at once;\n"
        "                            for more use temp files\n"),
      _("  -c, --check, --check=diagnose-first  check for sorted input; do not sort\n"
        "  -C, --check=quiet, --check=silent  like -c, but do not report first bad line\n"
        "      --compress-program=PROG  compress temporaries with PROG;\n"
        "                              decompress them with PROG -d\n"),
      _("      --debug               annotate the part of the line used to sort, and\n"
        "                              warn about questionable usage to standard error\n"
        "      --files0-from=F       read input from the files specified by\n"
        "                            NUL-terminated names in file F;\n"
        "                            If F is - then read names from standard input\n"),
      _("  -k, --key=KEYDEF          sort via a key; KEYDEF gives location and type\n"
        "  -m, --merge               merge already sorted files; do not sort\n"),
      _("  -o, --output=FILE         write result to FILE instead of standard output\n"
        "  -s, --stable              stabilize sort by disabling last-resort comparison\n"
        "  -S, --buffer-size=SIZE    use SIZE for main memory buffer\n"),
    };

    for (size_t i = 0; i < sizeof sections / sizeof sections[0]; i++)
      fputs (sections[i], stdout);
  }

  printf (_("  -t, --field-separator=SEP  use SEP instead of non-blank to blank transition\n"
            "  -T, --temporary-directory=DIR  use DIR for temporaries, not $TMPDIR or %s;\n"
            "                              multiple options specify multiple directories\n"
            "      --parallel=N          change the number of sorts run concurrently to N\n"
            "  -u, --unique              output only the first of lines with equal keys;\n"
            "                              with -c, check for strict ordering\n"),
          DEFAULT_TMPDIR);

  fputs (_("  -z, --zero-terminated     line delimiter is NUL, not newline\n"), stdout);
  fputs (HELP_OPTION_DESCRIPTION, stdout);
  fputs (VERSION_OPTION_DESCRIPTION, stdout);

  fputs (_("\n"
           "KEYDEF is F[.C][OPTS][,F[.C][OPTS]] for start and stop position, where F is a\n"
           "field number and C a character position in the field; both are origin 1, and\n"
           "the stop position defaults to the line's end.  If neither -t nor -b is in\n"
           "effect, characters in a field are counted from the beginning of the preceding\n"
           "whitespace.  OPTS is one or more single-letter ordering options [bdfgiMhnRrV],\n"
           "which override global ordering options for that key.  If no key is given, use\n"
           "the entire line as the key.  Use --debug to diagnose incorrect key usage.\n"
           "\n"
           "SIZE may be followed by the following multiplicative suffixes:\n"), stdout);

  fputs (_("% 1% of memory, b 1, K 1024 (default), and so on for M, G, T, P, E, Z, Y, R, Q.\n"
           "\n"
           "*** WARNING ***\n"
           "The locale specified by the environment affects sort order.\n"
           "Set LC_ALL=C to get the traditional sort order that uses\n"
           "native byte values.\n"), stdout);

  emit_ancillary_info (PROGRAM_NAME);

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
    return;

  status->valid = 0;

  if (pthread_sigmask (SIG_BLOCK, &caught_signals, &status->sigs) == 0)
    {
      status->valid = 1;
    }
  else
    {
      sigemptyset (&status->sigs);
    }
}

/* Leave a critical section.  */
static void
cs_leave (struct cs_status const *status)
{
  if (!status || !status->valid)
    return;

  (void) pthread_sigmask (SIG_SETMASK, &status->sigs, NULL);
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
proctab_hasher(const void *entry, size_t tabsize)
{
    if (tabsize == 0 || entry == NULL) {
        return 0;
    }
    const struct tempnode *node = (const struct tempnode *)entry;
    return ((size_t)node->pid) % tabsize;
}

static bool
proctab_comparator(const void *e1, const void *e2)
{
    if (e1 == e2) {
        return true;
    }
    if (e1 == NULL || e2 == NULL) {
        return false;
    }

    const struct tempnode *n1 = (const struct tempnode *)e1;
    const struct tempnode *n2 = (const struct tempnode *)e2;

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
  pid_t wait_target = (pid != 0) ? pid : (pid_t)-1;
  int wait_flags = (pid != 0) ? 0 : WNOHANG;

  pid_t cpid = waitpid (wait_target, &status, wait_flags);

  if (cpid < 0)
    {
      int saved_errno = errno;
      error (SORT_FAILURE, saved_errno, _("waiting for %s [-d]"),
             quoteaf (compress_program));
      return cpid;
    }

  if (cpid == 0)
    return 0;

  {
    int should_account = (pid > 0);
    if (! should_account)
      should_account = delete_proc (cpid);

    if (should_account)
      {
        if (! WIFEXITED (status) || WEXITSTATUS (status))
          error (SORT_FAILURE, 0, _("%s [-d] terminated abnormally"),
                 quoteaf (compress_program));
        --nprocs;
      }
  }

  return cpid;
}

/* TEMP represents a new process; add it to the process table.  Create
   the process table the first time it's called.  */

static void
register_proc(struct tempnode *temp)
{
  const void *result;

  if (temp == NULL)
    xalloc_die();

  if (proctab == NULL)
    {
      proctab = hash_initialize(INIT_PROCTAB_SIZE, NULL,
                                proctab_hasher,
                                proctab_comparator,
                                NULL);
      if (proctab == NULL)
        xalloc_die();
    }

  temp->state = UNREAPED;

  result = hash_insert(proctab, temp);
  if (result == NULL)
    xalloc_die();
}

/* If PID is in the process table, remove it and return true.
   Otherwise, return false.  */

static bool delete_proc(pid_t pid)
{
    struct tempnode test = { .pid = pid };
    struct tempnode *node;

    if (proctab == NULL) {
        return false;
    }

    node = hash_remove(proctab, &test);
    if (node == NULL) {
        return false;
    }

    node->state = REAPED;
    return true;
}

/* Remove PID from the process table, and wait for it to exit if it
   hasn't already.  */

static void
wait_proc(pid_t pid)
{
    if (!delete_proc(pid)) {
        return;
    }

    (void)reap(pid);
}

/* Reap any exited children.  Do not block; reap only those that have
   already exited.  */

static void
reap_exited(void)
{
    while (nprocs > 0) {
        if (reap(0) == 0) {
            break;
        }
    }
}

/* Reap at least one exited child, waiting if necessary.  */

static void reap_some(void)
{
    enum { REAP_ALL = -1 };
    (void)reap(REAP_ALL);
    (void)reap_exited();
}

/* Reap all children, waiting if necessary.  */

static void reap_all(void)
{
    const int REAP_ANY = -1;
    while (nprocs > 0) {
        reap(REAP_ANY);
    }
}

/* Clean up any remaining temporary files.  */

static void
cleanup (void)
{
  struct tempnode const *node;
  int saved_errno;

  saved_errno = errno;

  for (node = temphead; node; node = node->next)
    {
      if (node->name)
        {
          int rc;
          do
            {
              rc = unlink (node->name);
            }
          while (rc == -1 && errno == EINTR);
        }
    }
  temphead = NULL;
  errno = saved_errno;
}

/* Cleanup actions to take when exiting.  */

static void
exit_cleanup(void)
{
  int need_cleanup = temphead != 0;

  if (need_cleanup)
    {
      struct cs_status cs = (struct cs_status){0};
      cs_enter(&cs);
      cleanup();
      cs_leave(&cs);
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
  static const char slashbase[] = "/sortXXXXXX";
  static idx_t temp_dir_index;

  int fd = -1;
  int saved_errno;
  const char *temp_dir = temp_dirs[temp_dir_index];
  size_t len = strlen (temp_dir);
  struct tempnode *node =
    xmalloc (FLEXSIZEOF (struct tempnode, name, len + sizeof slashbase));
  char *file = node->name;
  struct cs_status cs;

  memcpy (file, temp_dir, len);
  memcpy (file + len, slashbase, sizeof slashbase);
  node->next = NULL;

  if (++temp_dir_index == temp_dir_count)
    temp_dir_index = 0;

  cs_enter (&cs);
  fd = mkostemp (file, O_CLOEXEC);
  if (fd >= 0)
    {
      *temptail = node;
      temptail = &node->next;
    }
  saved_errno = errno;
  cs_leave (&cs);
  errno = saved_errno;

  if (fd >= 0)
    {
      *pfd = fd;
      return node;
    }

  if (! (survive_fd_exhaustion && errno == EMFILE))
    error (SORT_FAILURE, errno, _("cannot create temporary file in %s"),
           quoteaf (temp_dir));

  free (node);
  *pfd = fd;
  return NULL;
}

/* Return a pointer to stdout status, or nullptr on failure.  */

static struct stat *
get_outstatus(void)
{
  static int initialized = 0;
  static int have_outstat = 0;
  static struct stat outstat;

  if (!initialized)
    {
      if (fstat(STDOUT_FILENO, &outstat) == 0)
        {
          have_outstat = 1;
        }
      else
        {
          have_outstat = 0;
        }
      initialized = 1;
    }

  return have_outstat ? &outstat : NULL;
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
  char mode = (how && *how) ? *how : '\0';

  if (mode == 'r')
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
                  int saved_errno = errno;
                  close (fd);
                  errno = saved_errno;
                }
            }
        }

      if (fp)
        fadvise (fp, FADVISE_SEQUENTIAL);
    }
  else if (mode == 'w')
    {
      if (file && ftruncate (STDOUT_FILENO, 0) != 0)
        {
          int ftruncate_errno = errno;
          struct stat *outst = get_outstatus ();
          if (!outst || S_ISREG (outst->st_mode) || S_TYPEISSHM (outst))
            error (SORT_FAILURE, ftruncate_errno, _("%s: error truncating"),
                   quotef (file));
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
  const char *fname = file ? file : "(null)";

  if (!file || !how)
    sort_die (_("open failed"), fname);

  FILE *fp = stream_open (fname, how);
  if (!fp)
    sort_die (_("open failed"), fname);
  return fp;
}

/* Close FP, whose name is FILE, and report any errors.  */

static void
xfclose (FILE *fp, char const *file)
{
  if (!fp)
    {
      sort_die (_("invalid file stream"), file);
      return;
    }

  int fd = fileno (fp);
  if (fd < 0)
    {
      sort_die (_("fileno failed"), file);
      return;
    }

  if (fd == STDIN_FILENO)
    {
      clearerr (fp);
      return;
    }

  if (fd == STDOUT_FILENO)
    {
      if (fflush (fp) != 0)
        sort_die (_("fflush failed"), file);
      return;
    }

  if (fclose (fp) != 0)
    sort_die (_("close failed"), file);
}

/* Move OLDFD to NEWFD.  If OLDFD != NEWFD, NEWFD is not close-on-exec.  */

static void
move_fd(int oldfd, int newfd)
{
    if (oldfd == newfd) {
        return;
    }
    (void)dup2(oldfd, newfd);
    (void)close(oldfd);
}

/* Fork a child process for piping to and do common cleanup.  The
   TRIES parameter specifies how many times to try to fork before
   giving up.  Return the PID of the child, or -1 (setting errno)
   on failure. */

static pid_t
pipe_fork (int pipefds[2], size_t tries)
{
#if HAVE_WORKING_FORK
  struct tempnode *saved_temphead;
  int saved_errno = 0;
  double wait_retry = 0.25;
  pid_t pid = -1;
  struct cs_status cs;

  if (pipe2 (pipefds, O_CLOEXEC) < 0)
    return -1;

  if (nmerge + 1 < nprocs)
    reap_some ();

  while (tries > 0)
    {
      --tries;

      cs_enter (&cs);
      saved_temphead = temphead;
      temphead = NULL;

      pid = fork ();
      saved_errno = errno;
      if (pid)
        temphead = saved_temphead;

      cs_leave (&cs);
      errno = saved_errno;

      if (pid >= 0 || errno != EAGAIN)
        break;

      xnanosleep (wait_retry);
      wait_retry *= 2;
      reap_exited ();
    }

  if (pid < 0)
    {
      saved_errno = errno;
      close (pipefds[0]);
      close (pipefds[1]);
      errno = saved_errno;
    }
  else if (pid == 0)
    {
      close (STDIN_FILENO);
      close (STDOUT_FILENO);
    }
  else
    {
      ++nprocs;
    }

  return pid;
#else
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
  int tempfd = -1;
  struct tempnode *node = create_temp_file (&tempfd, survive_fd_exhaustion);
  if (! node)
    return nullptr;

  node->state = UNCOMPRESSED;

  if (compress_program)
    {
      int pipefds[2] = { -1, -1 };

      node->pid = pipe_fork (pipefds, MAX_FORK_TRIES_COMPRESS);
      if (0 < node->pid)
        {
          close (tempfd);
          if (pipefds[0] >= 0)
            close (pipefds[0]);
          tempfd = pipefds[1];

          register_proc (node);
        }
      else if (node->pid == 0)
        {
          close (pipefds[1]);
          move_fd (tempfd, STDOUT_FILENO);
          move_fd (pipefds[0], STDIN_FILENO);

          execlp (compress_program, compress_program, (char *) nullptr);

          async_safe_die (errno, "couldn't execute compress program");
        }
      else
        {
          if (pipefds[0] >= 0)
            close (pipefds[0]);
          if (pipefds[1] >= 0)
            close (pipefds[1]);
        }
    }

  *pfp = fdopen (tempfd, "w");
  if (! *pfp)
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

static inline struct tempnode *
create_temp (FILE **pfp)
{
  return maybe_create_temp (pfp, false);
}

/* Open a compressed temp file and start a decompression process through
   which to filter the input.  Return nullptr (setting errno to
   EMFILE) if we ran out of file descriptors, and die on any other
   kind of failure.  */

static FILE *
open_temp(struct tempnode *temp)
{
  int tempfd, pipefds[2];
  FILE *fp = NULL;

  if (temp->state == UNREAPED)
    wait_proc(temp->pid);

  tempfd = open(temp->name, O_RDONLY);
  if (tempfd < 0)
    return NULL;

  pid_t child = pipe_fork(pipefds, MAX_FORK_TRIES_DECOMPRESS);

  if (child == -1)
    {
      if (errno != EMFILE)
        error(SORT_FAILURE, errno, _("couldn't create process for %s -d"),
              quoteaf(compress_program));
      close(tempfd);
      errno = EMFILE;
      return NULL;
    }

  if (child == 0)
    {
      close(pipefds[0]);
      move_fd(tempfd, STDIN_FILENO);
      move_fd(pipefds[1], STDOUT_FILENO);
      execlp(compress_program, compress_program, "-d", (char *) NULL);
      async_safe_die(errno, "couldn't execute compress program (with -d)");
    }

  temp->pid = child;
  register_proc(temp);
  close(tempfd);
  close(pipefds[1]);

  fp = fdopen(pipefds[0], "r");
  if (!fp)
    {
      int saved_errno = errno;
      close(pipefds[0]);
      errno = saved_errno;
      return NULL;
    }

  return fp;
}

/* Append DIR to the array of temporary directory names.  */
static void
add_temp_dir (char const *dir)
{
  if (temp_dir_count >= temp_dir_alloc)
    {
      temp_dirs = xpalloc (temp_dirs, &temp_dir_alloc, 1, -1, sizeof *temp_dirs);
    }

  temp_dirs[temp_dir_count] = dir;
  temp_dir_count++;
}

/* Remove NAME from the list of temporary files.  */

static void
zaptemp(const char *name)
{
  if (!name)
    return;

  struct tempnode *volatile *pnode = &temphead;
  struct tempnode *node = NULL;

  while ((node = *pnode) && node->name != name)
    pnode = &node->next;

  if (!node)
    return;

  if (node->state == UNREAPED)
    wait_proc(node->pid);

  struct tempnode *next = node->next;
  int unlink_status;
  int unlink_errno = 0;
  struct cs_status cs;

  cs_enter(&cs);
  unlink_status = unlink(name);
  if (unlink_status != 0)
    unlink_errno = errno;
  *pnode = next;
  cs_leave(&cs);

  if (unlink_status != 0)
    error(0, unlink_errno, _("warning: cannot remove: %s"), quotef(name));
  if (!next)
    temptail = pnode;

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

static void
inittables (void)
{
  size_t i;

  for (i = 0; i < UCHAR_LIM; ++i)
    {
      unsigned char uc = to_uchar (i);
      blanks[i] = (uc == '\n') || isblank (uc);
      nondictionary[i] = !blanks[i] && !isalnum (uc);
      nonprinting[i] = !isprint (uc);
      fold_toupper[i] = to_uchar (toupper (uc));
    }

#if HAVE_NL_LANGINFO
  if (hard_LC_TIME)
    {
      for (i = 0; i < MONTHS_PER_YEAR; i++)
        {
          char const *s = nl_langinfo (ABMON_1 + i);
          size_t s_len = strlen (s);
          size_t j;
          size_t k = 0;
          char *name = xmalloc (s_len + 1);

          monthtab[i].name = name;
          monthtab[i].val = i + 1;

          for (j = 0; j < s_len; j++)
            {
              unsigned char c = to_uchar (s[j]);
              if (!isblank (c))
                name[k++] = fold_toupper[c];
            }
          name[k] = '\0';
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
  struct rlimit rlimit;
  enum strtol_error e = xstrtoumax (s, NULL, 10, &n, "");

  rlim_t base_limit = 0;
  if (getrlimit (RLIMIT_NOFILE, &rlimit) == 0)
    base_limit = rlimit.rlim_cur;
  else
    base_limit = OPEN_MAX;

  unsigned int max_nmerge;
  if (base_limit <= 3)
    max_nmerge = 0;
  else
    {
      uintmax_t diff = (uintmax_t) base_limit - 3;
      max_nmerge = (unsigned int) diff;
    }

  if (e != LONGINT_OK)
    {
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
      return;
    }

  unsigned int requested = (unsigned int) n;
  if ((uintmax_t) requested != n)
    {
      error (0, 0, _("--%s argument %s too large"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("maximum --%s argument with current rlimit is %u"),
             long_options[oi].name, max_nmerge);
      return;
    }

  if (requested < 2)
    {
      error (0, 0, _("invalid --%s argument %s"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("minimum --%s argument is %s"),
             long_options[oi].name, quote ("2"));
      return;
    }

  if (requested > max_nmerge)
    {
      error (0, 0, _("--%s argument %s too large"),
             long_options[oi].name, quote (s));
      error (SORT_FAILURE, 0,
             _("maximum --%s argument with current rlimit is %u"),
             long_options[oi].name, max_nmerge);
      return;
    }

  nmerge = requested;
}

/* Specify the amount of main memory to use when sorting.  */
static void
specify_sort_size (int oi, char c, char const *s)
{
  uintmax_t n;
  char *suffix = NULL;
  enum strtol_error e = xstrtoumax (s, &suffix, 10, &n, "EgGkKmMPQRtTYZ");
  int last_digit = (suffix && suffix > s && c_isdigit ((unsigned char) suffix[-1]));

  if (e == LONGINT_OK && last_digit)
    {
      if (n <= UINTMAX_MAX / 1024)
        n *= 1024;
      else
        e = LONGINT_OVERFLOW;
    }
  else if (e == LONGINT_INVALID_SUFFIX_CHAR && last_digit && suffix[0] && !suffix[1])
    {
      switch (suffix[0])
        {
        case 'b':
          e = LONGINT_OK;
          break;

        case '%':
          {
            double mem = physmem_total () * n / 100;
            if (mem < UINTMAX_MAX)
              {
                n = mem;
                e = LONGINT_OK;
              }
            else
              e = LONGINT_OVERFLOW;
          }
          break;
        }
    }

  if (e == LONGINT_OK)
    {
      if (n < sort_size)
        return;

      sort_size = n;
      if (sort_size == n)
        {
          sort_size = MAX (sort_size, MIN_SORT_SIZE);
          return;
        }

      e = LONGINT_OVERFLOW;
    }

  xstrtol_fatal (e, oi, c, long_options, s);
}

/* Specify the number of threads to spawn during internal sort.  */
static size_t
specify_nthreads (int oi, char c, char const *s)
{
  uintmax_t nthreads = 0;
  enum strtol_error e = xstrtoumax (s, NULL, 10, &nthreads, "");

  switch (e)
    {
      case LONGINT_OK:
        break;
      case LONGINT_OVERFLOW:
        return SIZE_MAX;
      default:
        xstrtol_fatal (e, oi, c, long_options, s);
    }

  if (nthreads > SIZE_MAX)
    nthreads = SIZE_MAX;

  if (nthreads == 0)
    error (SORT_FAILURE, 0, _("number in parallel must be nonzero"));

  return (size_t) nthreads;
}

/* Return the default sort size.  */
static size_t min_size(size_t a, size_t b) {
  return a < b ? a : b;
}

static size_t clamp_rlimit_to_size(rlim_t v) {
  if ((rlim_t)0 > v)
    return 0;
  if (v > (rlim_t)SIZE_MAX)
    return SIZE_MAX;
  return (size_t)v;
}

static size_t clamp_double_to_size(double d) {
  if (d <= 0.0)
    return 0;
  if (d >= (double)SIZE_MAX)
    return SIZE_MAX;
  return (size_t)d;
}

static size_t
default_sort_size (void)
{
  size_t size = SIZE_MAX;
  struct rlimit rlimit;

  if (getrlimit (RLIMIT_DATA, &rlimit) == 0)
    size = min_size(size, clamp_rlimit_to_size(rlimit.rlim_cur));

#ifdef RLIMIT_AS
  if (getrlimit (RLIMIT_AS, &rlimit) == 0)
    size = min_size(size, clamp_rlimit_to_size(rlimit.rlim_cur));
#endif

  size /= 2;

#ifdef RLIMIT_RSS
  if (getrlimit (RLIMIT_RSS, &rlimit) == 0) {
    size_t rss = clamp_rlimit_to_size(rlimit.rlim_cur);
    size_t rss_margin = (rss / 16) * 15;
    size = min_size(size, rss_margin);
  }
#endif

  double avail = physmem_available ();
  double total = physmem_total ();
  if (avail < 0.0) avail = 0.0;
  if (total < 0.0) total = 0.0;

  size_t total_margin = (clamp_double_to_size(total) / 4) * 3;
  size = min_size(size, total_margin);

  double total_div_8 = total / 8.0;
  double mem_d = avail < total_div_8 ? total_div_8 : avail;
  size_t mem = clamp_double_to_size(mem_d);
  size = min_size(size, mem);

  return MAX (size, MIN_SORT_SIZE);
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
  static size_t size_bound;
  size_t worst_case_per_input_byte = line_bytes + 1;
  size_t size = worst_case_per_input_byte + 1;

  for (size_t i = 0; i < nfiles; i++)
    {
      struct stat st;
      int stat_res;

      if (i < nfps)
        stat_res = fstat (fileno (fps[i]), &st);
      else if (STREQ (files[i], "-"))
        stat_res = fstat (STDIN_FILENO, &st);
      else
        stat_res = stat (files[i], &st);

      if (stat_res != 0)
        sort_die (_("stat failed"), files[i]);

      int size_known = usable_st_size (&st) && 0 < st.st_size;
      size_t file_size_z;

      if (size_known)
        {
          if ((off_t) SIZE_MAX < st.st_size)
            {
              if (! size_bound)
                size_bound = sort_size ? sort_size : default_sort_size ();
              return size_bound;
            }
          file_size_z = (size_t) st.st_size;
        }
      else
        {
          if (sort_size)
            return sort_size;
          file_size_z = INPUT_FILE_SIZE_GUESS;
        }

      if (! size_bound)
        size_bound = sort_size ? sort_size : default_sort_size ();

      int overflow = 0;
      size_t worst_case = 0;

      if (file_size_z != 0 && worst_case_per_input_byte > SIZE_MAX / file_size_z)
        overflow = 1;
      else
        worst_case = file_size_z * worst_case_per_input_byte;

      if (! overflow)
        {
          if (worst_case == SIZE_MAX)
            overflow = 1;
          else
            worst_case += 1;
        }

      if (overflow)
        return size_bound;

      if (size_bound < size || worst_case > size_bound - size)
        return size_bound;

      size += worst_case;
    }

  return size;
}

/* Initialize BUF.  Reserve LINE_BYTES bytes for each line; LINE_BYTES
   must be at least sizeof (struct line).  Allocate ALLOC bytes
   initially.  */

static void
initbuf (struct buffer *buf, size_t line_bytes, size_t alloc)
{
  if (!buf)
    xalloc_die ();

  if (line_bytes > SIZE_MAX - 1)
    xalloc_die ();

  const size_t alignment = sizeof (struct line);
  const size_t min_alloc = line_bytes + 1;

  for (;;)
    {
      size_t remainder = alloc % alignment;
      size_t addition = alignment - remainder;

      if (alloc > SIZE_MAX - addition)
        xalloc_die ();

      size_t aligned_alloc = alloc + addition;

      buf->buf = malloc (aligned_alloc);
      if (buf->buf)
        {
          alloc = aligned_alloc;
          break;
        }

      alloc = aligned_alloc / 2;
      if (alloc <= min_alloc)
        xalloc_die ();
    }

  buf->line_bytes = line_bytes;
  buf->alloc = alloc;
  buf->used = 0;
  buf->left = 0;
  buf->nlines = 0;
  buf->eof = false;
}

/* Return one past the limit of the line array.  */

static inline struct line *
buffer_linelim(const struct buffer *buf)
{
    if (!buf || !buf->buf) {
        return NULL;
    }
    return (struct line *)((char *)buf->buf + buf->alloc);
}

/* Return a pointer to the first character of the field specified
   by KEY in LINE. */

static char *
begfield(struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text;
  char *lim = ptr;
  size_t sword = key->sword;
  size_t schar = key->schar;
  size_t i;

  if (line->length > 0)
    lim += line->length - 1;

  if (tab != TAB_DEFAULT)
    {
      for (i = 0; i < sword && ptr < lim; i++)
        {
          while (ptr < lim && *ptr != tab)
            ++ptr;
          if (ptr < lim)
            ++ptr;
        }
    }
  else
    {
      for (i = 0; i < sword && ptr < lim; i++)
        {
          while (ptr < lim && blanks[to_uchar(*ptr)])
            ++ptr;
          while (ptr < lim && !blanks[to_uchar(*ptr)])
            ++ptr;
        }
    }

  if (key->skipsblanks)
    while (ptr < lim && blanks[to_uchar(*ptr)])
      ++ptr;

  {
    size_t remaining_bytes = (ptr < lim) ? (size_t)(lim - ptr) : 0;
    if (schar < remaining_bytes)
      ptr += schar;
    else
      ptr = lim;
  }

  return ptr;
}

/* Return the limit of (a pointer to the first character after) the field
   in LINE specified by KEY. */

ATTRIBUTE_PURE
static char *
limfield (struct line const *line, struct keyfield const *key)
{
  char *ptr = line->text;
  char *lim = line->length ? ptr + line->length - 1 : ptr;
  size_t eword = key->eword, echar = key->echar;

  if (echar == 0)
    eword++;

  if (tab != TAB_DEFAULT)
    {
      size_t n = eword;
      while (ptr < lim && n > 0)
        {
          while (ptr < lim && *ptr != tab)
            ++ptr;
          if (ptr < lim && (n > 1 || echar))
            ++ptr;
          n--;
        }
    }
  else
    {
      size_t n = eword;
      while (ptr < lim && n > 0)
        {
          while (ptr < lim && blanks[to_uchar (*ptr)])
            ++ptr;
          while (ptr < lim && !blanks[to_uchar (*ptr)])
            ++ptr;
          n--;
        }
    }

#ifdef POSIX_UNSPECIFIED
  if (tab != TAB_DEFAULT)
    {
      char *newlim = memchr (ptr, tab, lim - ptr);
      if (newlim)
        lim = newlim;
    }
  else
    {
      char *newlim = ptr;
      while (newlim < lim && blanks[to_uchar (*newlim)])
        ++newlim;
      while (newlim < lim && !blanks[to_uchar (*newlim)])
        ++newlim;
      lim = newlim;
    }
#endif

  if (echar != 0)
    {
      if (key->skipeblanks)
        while (ptr < lim && blanks[to_uchar (*ptr)])
          ++ptr;

      ptrdiff_t diff = lim - ptr;
      size_t remaining_bytes = diff > 0 ? (size_t) diff : 0;
      if (echar < remaining_bytes)
        ptr += echar;
      else
        ptr = lim;
    }

  return ptr;
}

/* Fill BUF reading from FP, moving buf->left bytes from the end
   of buf->buf to the beginning first.  If EOF is reached and the
   file wasn't terminated by a newline, supply one.  Set up BUF's line
   table too.  FILE is the name of the file corresponding to FP.
   Return true if some input was read.  */

static bool
fillbuf (struct buffer *buf, FILE *fp, char const *file)
{
  struct keyfield const *key = keylist;
  char eol = eolchar;
  size_t line_bytes = buf->line_bytes;
  size_t mergesize = merge_buffer_size - MIN_MERGE_BUFFER_SIZE;

  if (buf->eof)
    return false;

  if (buf->used != buf->left)
    {
      memmove (buf->buf, buf->buf + buf->used - buf->left, buf->left);
      buf->used = buf->left;
      buf->nlines = 0;
    }

  for (;;)
    {
      char *ptr = buf->buf + buf->used;
      struct line *linelim = buffer_linelim (buf);
      struct line *line = linelim - buf->nlines;
      char *lines_space_start = (char *) linelim - buf->nlines * line_bytes;
      size_t avail = (size_t) (lines_space_start - ptr);
      char *line_start = buf->nlines ? line->text + line->length : buf->buf;

      while (line_bytes + 1 < avail)
        {
          size_t readsize = (avail - 1) / (line_bytes + 1);
          size_t bytes_read = fread (ptr, 1, readsize, fp);
          char *ptrlim = ptr + bytes_read;
          size_t span;
          char *p;

          avail -= bytes_read;

          if (bytes_read != readsize)
            {
              if (ferror (fp))
                sort_die (_("read failed"), file);
              if (feof (fp))
                {
                  buf->eof = true;
                  if (buf->buf == ptrlim)
                    return false;
                  if (line_start != ptrlim && ptrlim[-1] != eol)
                    {
                      *ptrlim++ = eol;
                    }
                }
            }

          for (;;)
            {
              span = (size_t) (ptrlim - ptr);
              if (span == 0)
                break;
              p = memchr (ptr, eol, span);
              if (!p)
                break;

              *p = '\0';
              ptr = p + 1;
              line--;
              line->text = line_start;
              line->length = (size_t) (ptr - line_start);
              mergesize = MAX (mergesize, line->length);
              avail -= line_bytes;

              if (key)
                {
                  line->keylim = (key->eword == SIZE_MAX
                                  ? p
                                  : limfield (line, key));

                  if (key->sword != SIZE_MAX)
                    {
                      line->keybeg = begfield (line, key);
                    }
                  else
                    {
                      if (key->skipsblanks)
                        {
                          while (blanks[to_uchar (*line_start)])
                            line_start++;
                        }
                      line->keybeg = line_start;
                    }
                }

              line_start = ptr;
            }

          ptr = ptrlim;
          if (buf->eof)
            break;
        }

      buf->used = (size_t) (ptr - buf->buf);
      buf->nlines = (size_t) (buffer_linelim (buf) - line);
      if (buf->nlines != 0)
        {
          buf->left = (size_t) (ptr - line_start);
          merge_buffer_size = mergesize + MIN_MERGE_BUFFER_SIZE;
          return true;
        }

      {
        idx_t line_alloc = buf->alloc / sizeof (struct line);
        buf->buf = xpalloc (buf->buf, &line_alloc, 1, -1, sizeof (struct line));
        buf->alloc = (size_t) line_alloc * sizeof (struct line);
      }
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
  if (!number || !*number)
    return '\0';

  char const *p = *number;
  char ch = *p++;
  char max_digit = '\0';
  bool ends_with_thousands_sep = false;

  while (c_isdigit (ch))
    {
      if (max_digit < ch)
        max_digit = ch;

      ends_with_thousands_sep = (*p == thousands_sep);
      if (ends_with_thousands_sep)
        ++p;

      ch = *p++;
    }

  if (ends_with_thousands_sep)
    {
      *number = p - 2;
      return max_digit;
    }

  if (ch == decimal_point)
    {
      ch = *p++;
      while (c_isdigit (ch))
        {
          if (max_digit < ch)
            max_digit = ch;
          ch = *p++;
        }
    }

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
  if (!number)
    return 0;

  bool minus_sign = (number[0] == '-');
  char const *p = number + (minus_sign ? 1 : 0);
  char max_digit = traverse_raw_number (&p);

  if (!(max_digit > '0'))
    return 0;

  unsigned char ch = (unsigned char) *p;
  int order = unit_order[ch];
  return minus_sign ? -order : order;
}

/* Compare numbers A and B ending in units with SI or IEC prefixes
       <none/unknown> < K/k < M < G < T < P < E < Z < Y < R < Q */

ATTRIBUTE_PURE
static int
human_numcompare (char const *a, char const *b)
{
  if (a == NULL || b == NULL)
    return (a == b) ? 0 : (a == NULL ? -1 : 1);

  while (blanks[to_uchar(*a)]) {
    a++;
  }
  while (blanks[to_uchar(*b)]) {
    b++;
  }

  const int order_a = find_unit_order(a);
  const int order_b = find_unit_order(b);

  if (order_a != order_b) {
    return (order_a < order_b) ? -1 : 1;
  }

  return strnumcmp(a, b, decimal_point, thousands_sep);
}

/* Compare strings A and B as numbers without explicitly converting them to
   machine numbers.  Comparatively slow for short strings, but asymptotically
   hideously fast. */

ATTRIBUTE_PURE
static inline char const *
skip_leading_blanks (char const *s)
{
  while (blanks[to_uchar (*s)])
    s++;
  return s;
}

ATTRIBUTE_PURE
static int
numcompare (char const *a, char const *b)
{
  a = skip_leading_blanks (a);
  b = skip_leading_blanks (b);

  return strnumcmp (a, b, decimal_point, thousands_sep);
}

#include <limits.h>
#include <stdio.h>
#include <string.h>

static int nan_compare(long double a, long double b)
{
    enum { OVERHEAD = sizeof "-nan" "()" };
    enum { BUF_SIZE = OVERHEAD + (CHAR_BIT * (int)sizeof a) };
    char buf0[BUF_SIZE];
    char buf1[BUF_SIZE];

    buf0[0] = '\0';
    buf1[0] = '\0';

    if (snprintf(buf0, sizeof buf0, "%Lf", a) < 0) {
        buf0[0] = '\0';
    }
    if (snprintf(buf1, sizeof buf1, "%Lf", b) < 0) {
        buf1[0] = '\0';
    }
    return strcmp(buf0, buf1);
}

static int
general_numcompare(const char *sa, const char *sb)
{
  char *ea;
  char *eb;
  long double a = strtold(sa, &ea);
  long double b = strtold(sb, &eb);

  if (sa == ea)
    return (sb == eb) ? 0 : -1;
  if (sb == eb)
    return 1;

  if (a < b)
    return -1;
  if (a > b)
    return 1;
  if (a == b)
    return 0;

  {
    int a_is_num = (a == a);
    int b_is_num = (b == b);

    if (b_is_num && !a_is_num)
      return -1;
    if (a_is_num && !b_is_num)
      return 1;
  }

  return nan_compare(a, b);
}

/* Return an integer in 1..12 of the month name MONTH.
   Return 0 if the name in S is not recognized.  */

static int
getmonth (char const *month, char **ea)
{
  if (!month)
    return 0;

  while (blanks[to_uchar(*month)])
    month++;

  size_t lo = 0;
  size_t hi = MONTHS_PER_YEAR;

  while (lo < hi)
    {
      size_t ix = lo + (hi - lo) / 2;
      char const *m = month;
      char const *n = monthtab[ix].name;
      int cmp = 0;

      while (*n)
        {
          unsigned char um = fold_toupper[to_uchar(*m)];
          unsigned char un = to_uchar(*n);

          if (um < un)
            {
              cmp = -1;
              break;
            }
          if (um > un)
            {
              cmp = 1;
              break;
            }

          m++;
          n++;
        }

      if (cmp == 0)
        {
          if (ea)
            *ea = (char *) m;
          return monthtab[ix].val;
        }

      if (cmp < 0)
        hi = ix;
      else
        lo = ix + 1;
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
link_libcrypto(void)
{
#if DLOPEN_LIBCRYPTO && HAVE_OPENSSL_MD5
  void *handle = dlopen(LIBCRYPTO_SONAME, RTLD_LAZY | RTLD_GLOBAL);
  if (!handle) {
    link_failure();
    return;
  }
  ptr_MD5_Init = symbol_address(handle, "MD5_Init");
  ptr_MD5_Update = symbol_address(handle, "MD5_Update");
  ptr_MD5_Final = symbol_address(handle, "MD5_Final");
#endif
}

/* A randomly chosen MD5 state, used for random comparison.  */
static struct md5_ctx random_md5_state;

/* Initialize the randomly chosen MD5 state.  */

static void
random_md5_state_init (char const *random_source)
{
  unsigned char seed[MD5_DIGEST_SIZE];
  struct randread_source *src = randread_new (random_source, sizeof seed);

  if (!src)
    {
      sort_die (_("open failed"), random_source ? random_source : "getrandom");
    }

  randread (src, seed, sizeof seed);

  if (randread_free (src) != 0)
    {
      sort_die (_("close failed"), random_source);
    }

  link_libcrypto ();
  md5_init_ctx (&random_md5_state);
  md5_process_bytes (seed, sizeof seed, &random_md5_state);

  memset (seed, 0, sizeof seed);
}

/* This is like strxfrm, except it reports any error and exits.  */

static size_t
xstrxfrm(char *restrict dest, char const *restrict src, size_t destsize)
{
  errno = 0;
  size_t translated_size = strxfrm(dest, src, destsize);

  if (errno == 0)
    return translated_size;

  int saved_errno = errno;
  error(0, saved_errno, _("string transformation failed"));
  error(0, 0, _("set LC_ALL='C' to work around the problem"));
  error(SORT_FAILURE, 0,
        _("the original string was %s"),
        quotearg_n_style(0, locale_quoting_style, src));

  return translated_size;
}

/* Compare the keys TEXTA (of length LENA) and TEXTB (of length LENB)
   using one or more random hash functions.  TEXTA[LENA] and
   TEXTB[LENB] must be zero.  */

static int
compare_random (char *restrict texta, size_t lena,
                char *restrict textb, size_t lenb)
{
  int xfrm_diff = 0;

  char stackbuf[4000];
  char *buf = stackbuf;
  size_t bufsize = sizeof stackbuf;
  void *allocated = NULL;
  uint32_t dig[2][MD5_DIGEST_SIZE / sizeof (uint32_t)];
  struct md5_ctx s[2];
  s[0] = s[1] = random_md5_state;

  if (hard_LC_COLLATE)
    {
      char const *lima = texta + lena;
      char const *limb = textb + lenb;

      while (true)
        {
          size_t sum = lena + lenb;
          size_t guess_bufsize;
          if (sum > (SIZE_MAX - 2) / 3)
            guess_bufsize = SIZE_MAX;
          else
            guess_bufsize = 3 * sum + 2;

          if (bufsize < guess_bufsize)
            {
              size_t grow = bufsize / 2;
              size_t newsize = bufsize + grow;
              if (newsize < bufsize)
                newsize = SIZE_MAX;
              bufsize = (guess_bufsize > newsize ? guess_bufsize : newsize);
              free (allocated);
              buf = allocated = malloc (bufsize);
              if (! buf)
                {
                  buf = stackbuf;
                  bufsize = sizeof stackbuf;
                  allocated = NULL;
                }
            }

          size_t sizea = (texta < lima ? xstrxfrm (buf, texta, bufsize) + 1 : 0);
          bool a_fits = sizea <= bufsize;
          size_t sizeb =
            (textb < limb
             ? (xstrxfrm ((a_fits ? buf + sizea : NULL), textb,
                          (a_fits ? bufsize - sizea : 0))
                + 1)
             : 0);

          if (! (a_fits && sizea + sizeb <= bufsize))
            {
              size_t needed = sizea + sizeb;
              if (needed < sizea)
                needed = SIZE_MAX;
              bufsize = needed;
              if (bufsize < SIZE_MAX / 3)
                {
                  size_t grow = bufsize / 2;
                  if (SIZE_MAX - bufsize >= grow)
                    bufsize += grow;
                  else
                    bufsize = SIZE_MAX;
                }
              free (allocated);
              buf = allocated = xmalloc (bufsize);
              if (texta < lima)
                strxfrm (buf, texta, sizea);
              if (textb < limb)
                strxfrm (buf + sizea, textb, sizeb);
            }

          if (texta < lima)
            texta += strlen (texta) + 1;
          if (textb < limb)
            textb += strlen (textb) + 1;
          if (! (texta < lima || textb < limb))
            {
              lena = sizea; texta = buf;
              lenb = sizeb; textb = buf + sizea;
              break;
            }

          md5_process_bytes (buf, sizea, &s[0]);
          md5_process_bytes (buf + sizea, sizeb, &s[1]);

          if (! xfrm_diff)
            {
              xfrm_diff = memcmp (buf, buf + sizea, MIN (sizea, sizeb));
              if (! xfrm_diff)
                xfrm_diff = _GL_CMP (sizea, sizeb);
            }
        }
    }

  md5_process_bytes (texta, lena, &s[0]); md5_finish_ctx (&s[0], dig[0]);
  md5_process_bytes (textb, lenb, &s[1]); md5_finish_ctx (&s[1], dig[1]);
  int diff = memcmp (dig[0], dig[1], sizeof dig[0]);

  if (! diff)
    {
      if (! xfrm_diff)
        {
          xfrm_diff = memcmp (texta, textb, MIN (lena, lenb));
          if (! xfrm_diff)
            xfrm_diff = _GL_CMP (lena, lenb);
        }

      diff = xfrm_diff;
    }

  free (allocated);

  return diff;
}

/* Return the printable width of the block of memory starting at
   TEXT and ending just before LIM, counting each tab as one byte.
   FIXME: Should we generally be counting non printable chars?  */

static size_t
debug_width(const char *text, const char *lim)
{
    if (!text || !lim || lim < text) {
        return 0;
    }

    size_t len = (size_t)(lim - text);
    size_t width = mbsnwidth(text, len, 0);

    size_t tab_count = 0;
    for (const char *p = text; p < lim; ++p) {
        if (*p == '\t') {
            ++tab_count;
        }
    }

    return width + tab_count;
}

/* For debug mode, "underline" a key at the
   specified offset and screen width.  */

static void
mark_key(size_t offset, size_t width)
{
    for (size_t i = 0; i < offset; ++i) {
        if (putchar(' ') == EOF) {
            return;
        }
    }

    if (width == 0) {
        if (printf(_("^ no match for key\n")) < 0) {
            return;
        }
        return;
    }

    for (size_t i = 0; i < width; ++i) {
        if (putchar('_') == EOF) {
            return;
        }
    }

    if (putchar('\n') == EOF) {
        return;
    }
}

/* Return true if KEY is a numeric key.  */

static inline bool
key_numeric(const struct keyfield *key)
{
    if (key == NULL) {
        return false;
    }
    return key->numeric || key->general_numeric || key->human_numeric;
}

/* For LINE, output a debugging line that underlines KEY in LINE.
   If KEY is null, underline the whole line.  */

static void
debug_key(struct line const *line, struct keyfield const *key)
{
  if (!line || !line->text) {
    mark_key(0, 0);
    return;
  }

  char *text = line->text;
  size_t len = line->length;

  if (len == 0) {
    mark_key(0, 0);
    return;
  }

  char *beg = text;
  char *lim = text + len - 1;

  if (key) {
    if (key->sword != SIZE_MAX)
      beg = begfield(line, key);

    if (key->eword != SIZE_MAX) {
      lim = limfield(line, key);
      if (lim < beg)
        lim = beg;
    }

    bool skip_blanks = (key->skipsblanks && key->sword == SIZE_MAX);
    bool need_tightening = (skip_blanks || key->month || key_numeric(key));

    if (need_tightening) {
      char saved = *lim;
      *lim = '\0';

      if (skip_blanks) {
        while (blanks[to_uchar(*beg)])
          beg++;
      }

      char *tighter_lim = lim;

      if (lim >= beg) {
        if (key->month) {
          getmonth(beg, &tighter_lim);
        } else if (key->general_numeric) {
          ignore_value(strtold(beg, &tighter_lim));
        } else if (key->numeric || key->human_numeric) {
          char const *p = beg + (beg < lim && *beg == '-');
          char max_digit = traverse_raw_number(&p);
          if ('0' <= max_digit) {
            unsigned char ch = *p;
            tighter_lim = (char *)p + (key->human_numeric && unit_order[ch]);
          }
        }
      }

      *lim = saved;
      lim = tighter_lim;
    }
  }

  size_t offset = debug_width(text, beg);
  size_t width = debug_width(beg, lim);
  mark_key(offset, width);
}

/* Debug LINE by underlining its keys.  */

static void
debug_line(struct line const *line)
{
  struct keyfield const *key = keylist;

  if (key == NULL)
    {
      debug_key(line, NULL);
      return;
    }

  for (;;)
    {
      debug_key(line, key);
      key = key->next;
      if (key == NULL)
        {
          if (!(unique || stable))
            {
              debug_key(line, NULL);
            }
          break;
        }
    }
}

/* Return whether sorting options specified for key.  */

static bool default_key_compare(const struct keyfield *key)
{
    if (key == NULL)
        return false;

    const bool has_any_option_set =
           key->ignore
        || key->translate
        || key->skipsblanks
        || key->skipeblanks
        || key_numeric(key)
        || key->month
        || key->version
        || key->random;

    return !has_any_option_set;
}

/* Convert a key to the short options used to specify it.  */

static void
key_to_opts (struct keyfield const *key, char *opts)
{
  if (!opts)
    return;
  if (!key)
  {
    *opts = '\0';
    return;
  }

  char *p = opts;
  struct { int cond; char flag; } map[] = {
    { key->skipsblanks || key->skipeblanks, 'b' },
    { key->ignore == nondictionary, 'd' },
    { key->translate, 'f' },
    { key->general_numeric, 'g' },
    { key->human_numeric, 'h' },
    { key->ignore == nonprinting, 'i' },
    { key->month, 'M' },
    { key->numeric, 'n' },
    { key->random, 'R' },
    { key->reverse, 'r' },
    { key->version, 'V' }
  };
  unsigned int i, n = (unsigned int)(sizeof map / sizeof map[0]);
  for (i = 0; i < n; i++)
    if (map[i].cond)
      *p++ = map[i].flag;

  *p = '\0';
}

/* Output data independent key warnings to stderr.  */

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
      bool is_numeric = key_numeric (key);

      if (is_numeric)
        {
          if (key->general_numeric)
            general_numeric_field = true;
          else
            basic_numeric_field = true;
        }

      if (key->traditional_used)
        {
          size_t sword = key->sword;
          size_t eword = key->eword;
          char tmp[INT_BUFSIZE_BOUND (uintmax_t)];
          char obuf[INT_BUFSIZE_BOUND (sword) * 2 + 4];
          char nbuf[INT_BUFSIZE_BOUND (sword) * 2 + 5];
          char *po = obuf;
          char *pn = nbuf;

          size_t sword_for_display = sword;
          if (sword_for_display == SIZE_MAX)
            sword_for_display++;

          po = stpcpy (stpcpy (po, "+"), umaxtostr (sword_for_display, tmp));
          pn = stpcpy (stpcpy (pn, "-k "), umaxtostr (sword_for_display + 1, tmp));

          if (eword != SIZE_MAX)
            {
              size_t eword_plus1 = eword + 1;
              stpcpy (stpcpy (po, " -"), umaxtostr (eword_plus1, tmp));
              size_t eword_plus1_maybe_inc = eword_plus1 + (key->echar == SIZE_MAX);
              stpcpy (stpcpy (pn, ","), umaxtostr (eword_plus1_maybe_inc, tmp));
            }

          error (0, 0, _("obsolescent key %s used; consider %s instead"),
                 quote_n (0, obuf), quote_n (1, nbuf));
        }

      bool zero_width = key->sword != SIZE_MAX && key->eword < key->sword;
      if (zero_width)
        error (0, 0, _("key %lu has zero width and will be ignored"), keynum);

      bool implicit_skip = is_numeric || key->month;
      bool line_offset = key->eword == 0 && key->echar != 0;
      bool leading_blanks_significant =
        !zero_width && !gkey_only && tab == TAB_DEFAULT && !line_offset
        && ((!key->skipsblanks && !implicit_skip)
            || (!key->skipsblanks && key->schar)
            || (!key->skipeblanks && key->echar));

      if (leading_blanks_significant)
        error (0, 0, _("leading blanks are significant in key %lu; consider also specifying 'b'"), keynum);

      if (!gkey_only && is_numeric)
        {
          size_t sword_plus1 = key->sword + 1;
          size_t eword_plus1 = key->eword + 1;
          if (!sword_plus1)
            sword_plus1++;
          if (!eword_plus1 || sword_plus1 < eword_plus1)
            {
              error (0, 0, _("key %lu is numeric and spans multiple fields"), keynum);
              if (key->general_numeric)
                general_numeric_field_span = true;
              else
                basic_numeric_field_span = true;
            }
        }

      if (ugkey.ignore && (ugkey.ignore == key->ignore))
        ugkey.ignore = NULL;
      if (ugkey.translate && (ugkey.translate == key->translate))
        ugkey.translate = NULL;
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

  bool number_locale_warned = false;
  if (basic_numeric_field_span)
    {
      if (tab == TAB_DEFAULT
          ? thousands_sep != NON_CHAR && (isblank (to_uchar (thousands_sep)))
          : tab == thousands_sep)
        {
          char sep[2] = { thousands_sep, 0 };
          error (0, 0,
                 _("field separator %s is treated as a group separator in numbers"),
                 quote (sep));
          number_locale_warned = true;
        }
    }
  if (basic_numeric_field_span || general_numeric_field_span)
    {
      if (tab == TAB_DEFAULT
          ? thousands_sep != NON_CHAR && (isblank (to_uchar (decimal_point)))
          : tab == decimal_point)
        {
          char sep[2] = { decimal_point, 0 };
          error (0, 0,
                 _("field separator %s is treated as a decimal point in numbers"),
                 quote (sep));
          number_locale_warned = true;
        }
      else if (tab == '-')
        {
          char sep[2] = { tab, 0 };
          error (0, 0,
                 _("field separator %s is treated as a minus sign in numbers"),
                 quote (sep));
        }
      else if (general_numeric_field_span && tab == '+')
        {
          char sep[2] = { tab, 0 };
          error (0, 0,
                 _("field separator %s is treated as a plus sign in numbers"),
                 quote (sep));
        }
    }

  if ((basic_numeric_field || general_numeric_field) && !number_locale_warned)
    {
      char sep[2] = { decimal_point, 0 };
      error (0, 0,
             _("numbers use %s as a decimal point in this locale"),
             quote (sep));
    }

  if (basic_numeric_field && thousands_sep_ignored)
    {
      error (0, 0,
             _("the multi-byte number group separator in this locale is not supported"));
    }

  if (!default_key_compare (&ugkey)
      || (ugkey.reverse && (stable || unique) && keylist))
    {
      bool ugkey_reverse = ugkey.reverse;
      if (!(stable || unique))
        ugkey.reverse = false;
      char opts[sizeof short_options];
      key_to_opts (&ugkey, opts);
      error (0, 0,
             ngettext ("option '-%s' is ignored",
                       "options '-%s' are ignored",
                       select_plural (strlen (opts))), opts);
      ugkey.reverse = ugkey_reverse;
    }

  if (ugkey.reverse && !(stable || unique) && keylist)
    error (0, 0, _("option '-r' only applies to last-resort comparison"));
}

/* Return either the sense of DIFF or its reverse, depending on REVERSED.
   If REVERSED, do not simply negate DIFF as that can mishandle INT_MIN.  */

static int
diff_reversed(int diff, bool reversed)
{
  if (reversed)
    {
      if (diff < 0)
        return 1;
      if (diff > 0)
        return -1;
      return 0;
    }
  return diff;
}

/* Compare two lines A and B trying every key in sequence until there
   are no more keys or a difference is found. */

static int compare_with_ignore(char const *texta, char const *lima,
                               char const *textb, char const *limb,
                               bool const *ignore, char const *translate)
{
  while (true)
    {
      while (texta < lima && ignore[to_uchar(*texta)])
        ++texta;
      while (textb < limb && ignore[to_uchar(*textb)])
        ++textb;

      if (! (texta < lima && textb < limb))
        return (texta < lima) - (textb < limb);

      int ca = translate ? to_uchar(translate[to_uchar(*texta)]) : to_uchar(*texta);
      int cb = translate ? to_uchar(translate[to_uchar(*textb)]) : to_uchar(*textb);
      int diff = ca - cb;
      if (diff)
        return diff;

      ++texta;
      ++textb;
    }
}

static int compare_translated_block(char const *texta, char const *textb,
                                    size_t len, char const *translate)
{
  for (size_t i = 0; i < len; i++)
    {
      int diff = to_uchar(translate[to_uchar(texta[i])])
               - to_uchar(translate[to_uchar(textb[i])]);
      if (diff)
        return diff;
    }
  return 0;
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
      char const *translate = key->translate;
      bool const *ignore = key->ignore;

      lima = MAX (texta, lima);
      limb = MAX (textb, limb);

      size_t lena = lima - texta;
      size_t lenb = limb - textb;

      if (hard_LC_COLLATE || key_numeric (key)
          || key->month || key->random || key->version)
        {
          char *ta = texta;
          char *tb = textb;
          size_t tlena = lena;
          size_t tlenb = lenb;
          char enda = ta[tlena];
          char endb = tb[tlenb];

          char *allocated = NULL;
          char stackbuf[4000];

          if (ignore || translate)
            {
              size_t size = lena + 1 + lenb + 1;
              if (size <= sizeof stackbuf)
                ta = stackbuf;
              else
                ta = allocated = xmalloc (size);
              tb = ta + lena + 1;

              tlena = 0;
              for (size_t i = 0; i < lena; i++)
                if (! (ignore && ignore[to_uchar (texta[i])]))
                  ta[tlena++] = translate ? translate[to_uchar (texta[i])] : texta[i];

              tlenb = 0;
              for (size_t i = 0; i < lenb; i++)
                if (! (ignore && ignore[to_uchar (textb[i])]))
                  tb[tlenb++] = translate ? translate[to_uchar (textb[i])] : textb[i];
            }

          ta[tlena] = '\0';
          tb[tlenb] = '\0';

          if (key->numeric)
            diff = numcompare (ta, tb);
          else if (key->general_numeric)
            diff = general_numcompare (ta, tb);
          else if (key->human_numeric)
            diff = human_numcompare (ta, tb);
          else if (key->month)
            diff = getmonth (ta, NULL) - getmonth (tb, NULL);
          else if (key->random)
            diff = compare_random (ta, tlena, tb, tlenb);
          else if (key->version)
            diff = filenvercmp (ta, tlena, tb, tlenb);
          else
            {
              if (tlena == 0)
                diff = - NONZERO (tlenb);
              else if (tlenb == 0)
                diff = 1;
              else
                diff = xmemcoll0 (ta, tlena + 1, tb, tlenb + 1);
            }

          ta[tlena] = enda;
          tb[tlenb] = endb;

          free (allocated);
        }
      else if (ignore)
        {
          diff = compare_with_ignore(texta, lima, textb, limb, ignore, translate);
        }
      else
        {
          size_t lenmin = MIN (lena, lenb);
          if (lenmin == 0)
            diff = 0;
          else if (translate)
            diff = compare_translated_block(texta, textb, lenmin, translate);
          else
            diff = memcmp (texta, textb, lenmin);

          if (! diff)
            diff = _GL_CMP (lena, lenb);
        }

      if (diff)
        break;

      key = key->next;
      if (! key)
        return 0;

      if (key->eword != SIZE_MAX)
        lima = limfield (a, key), limb = limfield (b, key);
      else
        lima = a->text + a->length - 1, limb = b->text + b->length - 1;

      if (key->sword != SIZE_MAX)
        texta = begfield (a, key), textb = begfield (b, key);
      else
        {
          texta = a->text, textb = b->text;
          if (key->skipsblanks)
            {
              while (texta < lima && blanks[to_uchar (*texta)])
                ++texta;
              while (textb < limb && blanks[to_uchar (*textb)])
                ++textb;
            }
        }
    }

  return diff_reversed (diff, key->reverse);
}

/* Compare two lines A and B, returning negative, zero, or positive
   depending on whether A compares less than, equal to, or greater than B. */

static int
compare (struct line const *a, struct line const *b)
{
  int diff;

  if (!a || !b)
    {
      int d = (a == b) ? 0 : (a ? 1 : -1);
      return keylist ? d : diff_reversed (d, reverse);
    }

  if (keylist)
    {
      diff = keycompare (a, b);
      if (diff || unique || stable)
        return diff;
    }

  size_t alen = (a->length > 0) ? a->length - 1 : 0;
  size_t blen = (b->length > 0) ? b->length - 1 : 0;

  if (alen == 0)
    {
      diff = - NONZERO (blen);
    }
  else if (blen == 0)
    {
      diff = 1;
    }
  else if (hard_LC_COLLATE)
    {
      diff = xmemcoll0 (a->text ? a->text : "", alen + 1,
                        b->text ? b->text : "", blen + 1);
    }
  else
    {
      size_t minlen = (alen < blen) ? alen : blen;
      const void *atext = a->text ? a->text : "";
      const void *btext = b->text ? b->text : "";
      diff = memcmp (atext, btext, minlen);
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
  if (!line || !fp)
    {
      sort_die (_("write failed"), output_file);
      return;
    }

  char *buf = line->text;
  size_t n_bytes = line->length;

  if (!output_file && debug)
    {
      if (n_bytes != 0 && !buf)
        {
          sort_die (_("write failed"), output_file);
          return;
        }

      char const *c = buf;
      char const *ebuf = buf + n_bytes;

      while (c < ebuf)
        {
          unsigned char uc = (unsigned char)*c++;
          int ch = (uc == '\t') ? '>' : (int)uc;
          if (uc != '\t' && c == ebuf)
            ch = '\n';
          if (fputc (ch, fp) == EOF)
            {
              sort_die (_("write failed"), output_file);
              return;
            }
        }

      debug_line (line);
      return;
    }

  if (n_bytes == 0)
    return;

  if (!buf)
    {
      sort_die (_("write failed"), output_file);
      return;
    }

  char *ebuf = buf + n_bytes;
  ebuf[-1] = eolchar;
  if (fwrite (buf, 1, n_bytes, fp) != n_bytes)
    {
      sort_die (_("write failed"), output_file);
      return;
    }
  ebuf[-1] = '\0';
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
  bool nonunique = ! unique;
  bool ordered = true;

  initbuf (&buf, sizeof (struct line), MAX (merge_buffer_size, sort_size));
  temp.text = NULL;

  while (fillbuf (&buf, fp, file_name))
    {
      struct line const *linelim = buffer_linelim (&buf);
      struct line const *line = linelim;
      struct line const *linebase = line - buf.nlines;

      if (alloc && nonunique <= compare (&temp, line - 1))
        {
        found_disorder:
          if (checkonly == 'c')
            {
              struct line const *disorder_line = line - 1;
              uintmax_t disorder_line_number = linelim - disorder_line + line_number;
              char hr_buf[INT_BUFSIZE_BOUND (disorder_line_number)];
              fprintf (stderr, _("%s: %s:%s: disorder: "),
                       program_name, file_name,
                       umaxtostr (disorder_line_number, hr_buf));
              write_line (disorder_line, stderr, _("standard error"));
            }

          ordered = false;
          break;
        }

      while (linebase < --line)
        if (nonunique <= compare (line, line - 1))
          goto found_disorder;

      line_number += buf.nlines;

      {
        size_t needed = line->length ? line->length : 1;
        if (alloc < needed)
          {
            size_t new_alloc = alloc ? alloc : 1;
            while (new_alloc < needed)
              {
                if (new_alloc > SIZE_MAX / 2)
                  {
                    new_alloc = needed;
                    break;
                  }
                new_alloc *= 2;
              }
            free (temp.text);
            temp.text = xmalloc (new_alloc);
            alloc = new_alloc;
          }
      }

      memcpy (temp.text, line->text, line->length);
      temp.length = line->length;
      if (keylist)
        {
          temp.keybeg = temp.text + (line->keybeg - line->text);
          temp.keylim = temp.text + (line->keylim - line->text);
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
  FILE **fps = xnmalloc (nfiles, sizeof *fps);
  *pfps = fps;

  size_t opened = 0;

  for (; opened < nfiles; opened++)
    {
      FILE *fp = (files[opened].temp && files[opened].temp->state != UNCOMPRESSED)
                 ? open_temp (files[opened].temp)
                 : stream_open (files[opened].name, "r");
      fps[opened] = fp;
      if (!fp)
        break;
    }

  return opened;
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   FPS is the vector of open stream corresponding to the files.
   Close input and output streams before returning.
   OUTPUT_FILE gives the name of the output file.  If it is null,
   the output file is standard output.  */

static inline void set_cur_base_for_index(size_t idx, struct buffer *buffer, struct line const **cur, struct line const **base)
{
  struct line const *linelim = buffer_linelim(&buffer[idx]);
  cur[idx] = linelim - 1;
  base[idx] = linelim - buffer[idx].nlines;
}

static inline void ensure_saved_capacity(struct line *saved, size_t *savealloc, size_t needed)
{
  if (*savealloc >= needed)
    return;

  size_t cap = *savealloc ? *savealloc : needed;
  while (cap < needed)
    {
      size_t newcap = cap * 2;
      if (newcap <= cap)
        {
          cap = needed;
          break;
        }
      cap = newcap;
    }

  free(saved->text);
  saved->text = xmalloc(cap);
  *savealloc = cap;
}

static void
mergefps (struct sortfile *files, size_t ntemps, size_t nfiles,
          FILE *ofp, char const *output_file, FILE **fps)
{
  struct buffer *buffer = xnmalloc (nfiles, sizeof *buffer);
  struct line saved;
  struct line const *savedline = NULL;
  size_t savealloc = 0;
  struct line const **cur = xnmalloc (nfiles, sizeof *cur);
  struct line const **base = xnmalloc (nfiles, sizeof *base);
  size_t *ord = xnmalloc (nfiles, sizeof *ord);
  size_t i;
  size_t j;
  struct keyfield const *key = keylist;

  saved.text = NULL;

  /* Read initial lines from each input file. */
  for (i = 0; i < nfiles; )
    {
      initbuf (&buffer[i], sizeof (struct line),
               MAX (merge_buffer_size, sort_size / nfiles));

      if (fillbuf (&buffer[i], fps[i], files[i].name))
        {
          set_cur_base_for_index(i, buffer, cur, base);
          i++;
        }
      else
        {
          /* fps[i] is empty; eliminate it from future consideration.  */
          xfclose (fps[i], files[i].name);
          if (i < ntemps)
            {
              ntemps--;
              zaptemp (files[i].name);
            }
          free (buffer[i].buf);
          --nfiles;
          for (j = i; j < nfiles; ++j)
            {
              files[j] = files[j + 1];
              fps[j] = fps[j + 1];
            }
        }
    }

  /* Initialize ord to 0..nfiles-1. */
  for (i = 0; i < nfiles; ++i)
    ord[i] = i;

  /* Stable insertion sort of ord based on initial lines. */
  for (i = 1; i < nfiles; ++i)
    {
      size_t key_idx = ord[i];
      size_t k = i;
      while (k > 0 && 0 < compare (cur[ord[k - 1]], cur[key_idx]))
        {
          ord[k] = ord[k - 1];
          --k;
        }
      ord[k] = key_idx;
    }

  /* Repeatedly output the smallest line until no input remains. */
  while (nfiles)
    {
      size_t ord0 = ord[0];
      struct line const *smallest = cur[ord0];

      /* If uniquified output is turned on, output only the first of
         an identical series of lines. */
      if (unique)
        {
          if (savedline && compare (savedline, smallest))
            {
              savedline = NULL;
              write_line (&saved, ofp, output_file);
            }
          if (!savedline)
            {
              savedline = &saved;
              ensure_saved_capacity(&saved, &savealloc, smallest->length);
              saved.length = smallest->length;
              memcpy (saved.text, smallest->text, saved.length);
              if (key)
                {
                  saved.keybeg = saved.text + (smallest->keybeg - smallest->text);
                  saved.keylim = saved.text + (smallest->keylim - smallest->text);
                }
            }
        }
      else
        {
          write_line (smallest, ofp, output_file);
        }

      /* Check if we need to read more lines into memory. */
      if (base[ord0] < smallest)
        {
          cur[ord0] = smallest - 1;
        }
      else
        {
          if (fillbuf (&buffer[ord0], fps[ord0], files[ord0].name))
            {
              set_cur_base_for_index(ord0, buffer, cur, base);
            }
          else
            {
              /* We reached EOF on fps[ord0].  Adjust ord indexes > ord0. */
              for (i = 1; i < nfiles; ++i)
                if (ord[i] > ord0)
                  --ord[i];

              /* Remove file ord0. */
              --nfiles;
              xfclose (fps[ord0], files[ord0].name);
              if (ord0 < ntemps)
                {
                  ntemps--;
                  zaptemp (files[ord0].name);
                }
              free (buffer[ord0].buf);

              for (i = ord0; i < nfiles; ++i)
                {
                  fps[i] = fps[i + 1];
                  files[i] = files[i + 1];
                  buffer[i] = buffer[i + 1];
                  cur[i] = cur[i + 1];
                  base[i] = base[i + 1];
                }
              for (i = 0; i < nfiles; ++i)
                ord[i] = ord[i + 1];

              continue;
            }
        }

      /* Reposition ord0 among ord[1..nfiles-1] using binary search with stable tie-breaker. */
      {
        size_t lo = 1;
        size_t hi = nfiles;
        size_t probe = lo;

        while (lo < hi)
          {
            int cmp = compare (cur[ord0], cur[ord[probe]]);
            if (cmp < 0 || (cmp == 0 && ord0 < ord[probe]))
              hi = probe;
            else
              lo = probe + 1;
            probe = (lo + hi) / 2;
          }

        size_t count_of_smaller_lines = lo - 1;
        for (j = 0; j < count_of_smaller_lines; j++)
          ord[j] = ord[j + 1];
        ord[count_of_smaller_lines] = ord0;
      }
    }

  if (unique && savedline)
    {
      write_line (&saved, ofp, output_file);
      free (saved.text);
    }

  xfclose (ofp, output_file);
  free (fps);
  free (buffer);
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

  if (nopened < nfiles && nopened < 2)
    {
      sort_die (_("open failed"), files[nopened].name);
      return nopened;
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
mergelines(struct line *restrict t, size_t nlines,
           struct line const *restrict lo)
{
  if (nlines <= 1)
    return;

  size_t nlo = nlines / 2;
  size_t nhi = nlines - nlo;
  struct line *hi = t - nlo;

  while (nlo != 0 && nhi != 0)
    {
      const struct line *lo_prev = lo - 1;
      const struct line *hi_prev = hi - 1;

      if (compare(lo_prev, hi_prev) <= 0)
        {
          --t;
          --lo;
          *t = *lo;
          --nlo;
        }
      else
        {
          --t;
          --hi;
          *t = *hi;
          --nhi;
        }
    }

  while (nlo != 0)
    {
      --t;
      --lo;
      *t = *lo;
      --nlo;
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
sequential_sort(struct line *restrict lines, size_t nlines,
                struct line *restrict temp, bool to_temp)
{
    if (nlines <= 1) {
        if (nlines == 1 && !to_temp) {
            temp[-1] = lines[-1];
        }
        return;
    }

    if (nlines == 2) {
        int swap = (0 < compare(&lines[-1], &lines[-2]));
        if (to_temp) {
            temp[-1] = lines[-1 - swap];
            temp[-2] = lines[-2 + swap];
        } else if (swap) {
            struct line t = lines[-1];
            lines[-1] = lines[-2];
            lines[-2] = t;
        }
        return;
    }

    size_t nlo = nlines / 2;
    size_t nhi = nlines - nlo;

    struct line *lo = lines;
    struct line *hi = lines - nlo;

    struct line *temp_for_hi = to_temp ? temp - nlo : temp;
    sequential_sort(hi, nhi, temp_for_hi, to_temp);

    if (nlo > 1) {
        sequential_sort(lo, nlo, temp, !to_temp);
    } else if (!to_temp) {
        temp[-1] = lo[-1];
    }

    struct line *dest = to_temp ? temp : lines;
    struct line const *sorted_lo = to_temp ? lines : temp;

    mergelines(dest, nlines, sorted_lo);
}

static struct merge_node *init_node (struct merge_node *restrict,
                                     struct merge_node *restrict,
                                     struct line *, size_t, size_t, bool);


/* Create and return a merge tree for NTHREADS threads, sorting NLINES
   lines, with destination DEST.  */
static struct merge_node *
merge_tree_init(size_t nthreads, size_t nlines, struct line *dest)
{
  if (nthreads == 0)
    return NULL;

  if (nthreads > SIZE_MAX / 2)
    return NULL;

  size_t total_nodes = nthreads * 2;
  if (total_nodes > SIZE_MAX / sizeof(struct merge_node))
    return NULL;

  size_t bytes = total_nodes * sizeof(struct merge_node);
  struct merge_node *merge_tree = xmalloc(bytes);
  if (!merge_tree)
    return NULL;

  memset(merge_tree, 0, bytes);

  struct merge_node *root = merge_tree;
  root->nlo = nlines;
  root->nhi = nlines;
  root->level = MERGE_END;

  if (pthread_mutex_init(&root->lock, NULL) != 0) {
    free(merge_tree);
    return NULL;
  }

  init_node(root, root + 1, dest, nthreads, nlines, false);
  return merge_tree;
}

/* Destroy the merge tree. */
static void
merge_tree_destroy (size_t nthreads, struct merge_node *merge_tree)
{
  if (merge_tree == NULL)
    return;

  if (nthreads > ((size_t)-1) / 2)
    {
      free (merge_tree);
      return;
    }

  size_t n_nodes = nthreads * 2;

  for (size_t i = 0; i < n_nodes; i++)
    (void) pthread_mutex_destroy (&merge_tree[i].lock);

  free (merge_tree);
}

/* Initialize a merge tree node and its descendants.  The node's
   parent is PARENT.  The node and its descendants are taken from the
   array of nodes NODE_POOL.  Their destination starts at DEST; they
   will consume NTHREADS threads.  The total number of sort lines is
   TOTAL_LINES.  IS_LO_CHILD is true if the node is the low child of
   its parent.  */

static struct merge_node *
init_node(struct merge_node *restrict parent,
          struct merge_node *restrict node_pool,
          struct line *dest, size_t nthreads,
          size_t total_lines, bool is_lo_child)
{
  size_t nlines = is_lo_child ? parent->nlo : parent->nhi;
  size_t nlo = nlines / 2;
  size_t nhi = nlines - nlo;
  struct line *lo = dest - total_lines;
  struct line *hi = lo - nlo;
  struct line **parent_end = is_lo_child ? &parent->end_lo : &parent->end_hi;

  struct merge_node *node = node_pool++;
  node->lo = lo;
  node->end_lo = lo;
  node->hi = hi;
  node->end_hi = hi;
  node->dest = parent_end;
  node->nlo = nlo;
  node->nhi = nhi;
  node->parent = parent;
  node->level = parent->level + 1;
  node->queued = false;
  node->lo_child = NULL;
  node->hi_child = NULL;

  if (pthread_mutex_init(&node->lock, NULL) != 0)
    return node_pool;

  if (nthreads > 1)
    {
      size_t lo_threads = nthreads / 2;
      size_t hi_threads = nthreads - lo_threads;

      node->lo_child = node_pool;
      node_pool = init_node(node, node_pool, lo, lo_threads, total_lines, true);

      node->hi_child = node_pool;
      node_pool = init_node(node, node_pool, hi, hi_threads, total_lines, false);
    }

  return node_pool;
}


/* Compare two merge nodes A and B for priority.  */

static int compare_nodes(const void *a, const void *b)
{
    const struct merge_node *nodea = (const struct merge_node *)a;
    const struct merge_node *nodeb = (const struct merge_node *)b;

    if (nodea == nodeb) return 0;
    if (nodea == NULL) return -1;
    if (nodeb == NULL) return 1;

    if (nodea->level < nodeb->level) return -1;
    if (nodea->level > nodeb->level) return 1;

    long long sa = (long long)nodea->nlo + (long long)nodea->nhi;
    long long sb = (long long)nodeb->nlo + (long long)nodeb->nhi;

    if (sa < sb) return -1;
    if (sa > sb) return 1;
    return 0;
}

/* Lock a merge tree NODE.  */

#include <assert.h>
#include <pthread.h>

static inline void lock_node(struct merge_node *node)
{
    assert(node != NULL);
    int rc = pthread_mutex_lock(&node->lock);
    assert(rc == 0);
}

/* Unlock a merge tree NODE. */

static inline void
unlock_node(struct merge_node *node)
{
  assert(node != NULL);
  int rc = pthread_mutex_unlock(&node->lock);
  assert(rc == 0);
}

/* Destroy merge QUEUE. */

static void
queue_destroy(struct merge_node_queue *queue)
{
  if (queue == NULL)
    return;

  if (queue->priority_queue != NULL)
  {
    heap_free(queue->priority_queue);
    queue->priority_queue = NULL;
  }

  (void)pthread_cond_destroy(&queue->cond);
  (void)pthread_mutex_destroy(&queue->mutex);
}

/* Initialize merge QUEUE, allocating space suitable for a maximum of
   NTHREADS threads.  */

static void
queue_init(struct merge_node_queue *queue, size_t nthreads)
{
    if (queue == NULL) {
        return;
    }

    if (pthread_mutex_init(&queue->mutex, NULL) != 0) {
        return;
    }

    if (pthread_cond_init(&queue->cond, NULL) != 0) {
        pthread_mutex_destroy(&queue->mutex);
        return;
    }

    size_t capacity = nthreads > ((size_t)-1 / 2) ? (size_t)-1 : nthreads * 2;
    queue->priority_queue = heap_alloc(compare_nodes, capacity);
}

/* Insert NODE into QUEUE.  The caller either holds a lock on NODE, or
   does not need to lock NODE.  */

static void
queue_insert (struct merge_node_queue *queue, struct merge_node *node)
{
  if (queue == NULL || node == NULL)
    {
      return;
    }

  if (pthread_mutex_lock (&queue->mutex) != 0)
    {
      return;
    }

  if (queue->priority_queue == NULL)
    {
      (void) pthread_mutex_unlock (&queue->mutex);
      return;
    }

  heap_insert (queue->priority_queue, node);
  node->queued = true;

  (void) pthread_cond_signal (&queue->cond);
  (void) pthread_mutex_unlock (&queue->mutex);
}

/* Pop the top node off the priority QUEUE, lock the node, return it.  */

static struct merge_node *
queue_pop(struct merge_node_queue *queue)
{
    struct merge_node *node = NULL;
    int rc;

    if (queue == NULL || queue->priority_queue == NULL) {
        return NULL;
    }

    rc = pthread_mutex_lock(&queue->mutex);
    if (rc != 0) {
        return NULL;
    }

    node = heap_remove_top(queue->priority_queue);
    while (node == NULL) {
        rc = pthread_cond_wait(&queue->cond, &queue->mutex);
        if (rc != 0) {
            pthread_mutex_unlock(&queue->mutex);
            return NULL;
        }
        node = heap_remove_top(queue->priority_queue);
    }

    rc = pthread_mutex_unlock(&queue->mutex);
    if (rc != 0) {
        return NULL;
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
write_unique(struct line const *line, FILE *tfp, char const *temp_output)
{
    if (!line || !tfp || !temp_output) {
        return;
    }

    if (unique && saved_line.text) {
        int compare_result = compare(line, &saved_line);
        if (compare_result == 0) {
            return;
        }
    }

    if (unique) {
        saved_line = *line;
    }

    write_line(line, tfp, temp_output);
}

/* Merge the lines currently available to a NODE in the binary
   merge tree.  Merge a number of lines appropriate for this merge
   level, assuming TOTAL_LINES is the total number of lines.

   If merging at the top level, send output to TFP.  TEMP_OUTPUT is
   the name of TFP, or is null if TFP is standard output.  */

static inline void emit_line(struct merge_node *restrict node, int from_lo,
                             struct line **dest, FILE *tfp,
                             char const *temp_output, int to_dest)
{
  if (to_dest)
    {
      if (from_lo)
        *--(*dest) = *--node->lo;
      else
        *--(*dest) = *--node->hi;
    }
  else
    {
      if (from_lo)
        write_unique (--node->lo, tfp, temp_output);
      else
        write_unique (--node->hi, tfp, temp_output);
    }
}

static void
mergelines_node (struct merge_node *restrict node, size_t total_lines,
                 FILE *tfp, char const *temp_output)
{
  struct line *lo_orig = node->lo;
  struct line *hi_orig = node->hi;
  size_t to_merge = MAX_MERGE (total_lines, node->level);
  size_t merged_lo;
  size_t merged_hi;

  int to_dest = (node->level > MERGE_ROOT);
  struct line *dest = to_dest ? *node->dest : NULL;

  while (node->lo != node->end_lo && node->hi != node->end_hi && to_merge-- > 0)
    {
      int from_lo = (compare (node->lo - 1, node->hi - 1) <= 0);
      emit_line (node, from_lo, &dest, tfp, temp_output, to_dest);
    }

  merged_lo = lo_orig - node->lo;
  merged_hi = hi_orig - node->hi;

  if (node->nhi == merged_hi)
    {
      while (node->lo != node->end_lo && to_merge-- > 0)
        emit_line (node, 1, &dest, tfp, temp_output, to_dest);
    }
  else if (node->nlo == merged_lo)
    {
      while (node->hi != node->end_hi && to_merge-- > 0)
        emit_line (node, 0, &dest, tfp, temp_output, to_dest);
    }

  if (to_dest)
    *node->dest = dest;

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

  const bool lo_avail = (node->lo != node->end_lo);
  const bool hi_avail = (node->hi != node->end_hi);

  if (lo_avail)
    {
      if (hi_avail || ! node->nhi)
        queue_insert (queue, node);
      return;
    }

  if (hi_avail && ! node->nlo)
    queue_insert (queue, node);
}

/* Into QUEUE, insert NODE's parent if the parent can now be worked on.  */

static void queue_check_insert_parent(struct merge_node_queue *queue, struct merge_node *node)
{
    if (queue == NULL || node == NULL) {
        return;
    }

    struct merge_node *parent = node->parent;
    if (parent == NULL) {
        return;
    }

    if (node->level > MERGE_ROOT) {
        lock_node(parent);
        queue_check_insert(queue, parent);
        unlock_node(parent);
        return;
    }

    if (node->nlo == 0 && node->nhi == 0) {
        queue_insert(queue, parent);
    }
}

/* Repeatedly pop QUEUE for a node with lines to merge, and merge at least
   some of those lines, until the MERGE_END node is popped.
   TOTAL_LINES is the total number of lines.  If merging at the top
   level, send output to TFP.  TEMP_OUTPUT is the name of TFP, or is
   null if TFP is standard output.  */

static void
merge_loop(struct merge_node_queue *queue,
           size_t total_lines, FILE *tfp, char const *temp_output)
{
  if (!queue || !tfp || !temp_output)
    return;

  for (;;)
    {
      struct merge_node *node = queue_pop(queue);
      if (!node)
        continue;

      if (node->level == MERGE_END)
        {
          unlock_node(node);
          queue_insert(queue, node);
          break;
        }

      mergelines_node(node, total_lines, tfp, temp_output);
      queue_check_insert(queue, node);
      queue_check_insert_parent(queue, node);
      unlock_node(node);
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
sortlines_thread(void *data)
{
  if (data == NULL) {
    return NULL;
  }

  const struct thread_args *args = (const struct thread_args *) data;

  sortlines(args->lines, args->nthreads, args->total_lines,
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
sortlines(struct line *restrict lines, size_t nthreads,
          size_t total_lines, struct merge_node *node,
          struct merge_node_queue *queue, FILE *tfp, char const *temp_output)
{
  size_t nlines = node->nlo + node->nhi;

  if (nthreads > 1 && nlines >= SUBTHREAD_LINES_HEURISTIC)
    {
      size_t lo_threads = nthreads / 2;
      size_t hi_threads = nthreads - lo_threads;
      pthread_t thread;
      struct thread_args *pargs = malloc(sizeof *pargs);
      int started = 0;

      if (pargs)
        {
          *pargs = (struct thread_args){lines, lo_threads, total_lines,
                                        node->lo_child, queue, tfp, temp_output};
          if (pthread_create(&thread, NULL, sortlines_thread, pargs) == 0)
            started = 1;
          else
            free(pargs);
        }

      if (started)
        {
          sortlines(lines - node->nlo, hi_threads, total_lines,
                    node->hi_child, queue, tfp, temp_output);
          pthread_join(thread, NULL);
          free(pargs);
          return;
        }
    }

  size_t nlo = node->nlo;
  size_t nhi = node->nhi;
  struct line *temp = lines - total_lines;

  if (nhi > 1)
    sequential_sort(lines - nlo, nhi, temp - nlo / 2, false);
  if (nlo > 1)
    sequential_sort(lines, nlo, temp, false);

  node->lo = lines;
  node->hi = lines - nlo;
  node->end_lo = lines - nlo;
  node->end_hi = lines - nlo - nhi;

  queue_insert(queue, node);
  merge_loop(queue, total_lines, tfp, temp_output);
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
avoid_trashing_input(struct sortfile *files, size_t ntemps, size_t nfiles, char const *outfile)
{
  if (!files || ntemps >= nfiles)
    return;

  struct tempnode *tempcopy = NULL;

  for (size_t i = ntemps; i < nfiles; i++)
    {
      struct sortfile *sf = &files[i];
      bool is_stdin = STREQ(sf->name, "-");
      bool same = false;

      if (outfile && STREQ(outfile, sf->name) && !is_stdin)
        {
          same = true;
        }
      else
        {
          struct stat *outst = get_outstatus();
          if (!outst)
            break;

          struct stat instat;
          int s = is_stdin ? fstat(STDIN_FILENO, &instat) : stat(sf->name, &instat);
          if (s == 0 && psame_inode(&instat, outst))
            same = true;
        }

      if (!same)
        continue;

      if (!tempcopy)
        {
          FILE *tftp = NULL;
          tempcopy = create_temp(&tftp);
          if (!tempcopy || !tftp)
            break;
          mergefiles(sf, 0, 1, tftp, tempcopy->name);
        }

      sf->name = tempcopy->name;
      sf->temp = tempcopy;
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
      const char *file = files[i];

      if (file && STREQ (file, "-"))
        continue;

      if (!file || euidaccess (file, R_OK) != 0)
        sort_die (_("cannot read"), file);
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

  const int open_flags = O_WRONLY | O_BINARY | O_CLOEXEC | O_CREAT;
  int outfd = open (outfile, open_flags, MODE_RW_UGO);
  if (outfd < 0)
    {
      sort_die (_("open failed"), outfile);
      return;
    }

  if (move_fd (outfd, STDOUT_FILENO) < 0)
    {
      int saved_errno = errno;
      close (outfd);
      errno = saved_errno;
      sort_die (_("fd move failed"), outfile);
    }
}

/* Merge the input FILES.  NTEMPS is the number of files at the
   start of FILES that are temporary; it is zero at the top level.
   NFILES is the total number of files.  Put the output in
   OUTPUT_FILE; a null OUTPUT_FILE stands for standard output.  */

static inline size_t min_size_t(size_t a, size_t b) { return a < b ? a : b; }

static size_t merge_into_temp(struct sortfile *files, size_t in_idx, size_t out_idx,
                              size_t *p_ntemps, size_t m)
{
  FILE *tfp;
  struct tempnode *temp = create_temp(&tfp);
  size_t limit = min_size_t(*p_ntemps, m);
  size_t num_merged = mergefiles(&files[in_idx], limit, m, tfp, temp->name);
  size_t consumed = min_size_t(*p_ntemps, num_merged);
  *p_ntemps -= consumed;
  files[out_idx].name = temp->name;
  files[out_idx].temp = temp;
  return num_merged;
}

static void
merge (struct sortfile *files, size_t ntemps, size_t nfiles,
       char const *output_file)
{
  size_t merge_factor = nmerge ? nmerge : 1;

  while (merge_factor < nfiles)
    {
      size_t in = 0;
      size_t out = 0;

      for (; merge_factor <= nfiles - in; out++)
        {
          size_t num_merged = merge_into_temp(files, in, out, &ntemps, merge_factor);
          in += num_merged;
        }

      {
        size_t remainder = nfiles - in;
        size_t cheap_slots = merge_factor - (out % merge_factor);

        if (cheap_slots < remainder)
          {
            size_t nshortmerge = remainder - cheap_slots + 1;
            size_t num_merged = merge_into_temp(files, in, out, &ntemps, nshortmerge);
            out++;
            in += num_merged;
          }

        if (nfiles > in)
          memmove(&files[out], &files[in], (nfiles - in) * sizeof *files);

        ntemps += out;
        nfiles -= in - out;
      }
    }

  avoid_trashing_input(files, ntemps, nfiles, output_file);

  for (;;)
    {
      FILE **fps;
      size_t nopened = open_input_files(files, nfiles, &fps);

      if (nopened == nfiles)
        {
          FILE *ofp = stream_open(output_file, "w");
          if (ofp)
            {
              mergefps(files, ntemps, nfiles, ofp, output_file, fps);
              break;
            }
          if (errno != EMFILE || nopened <= 2)
            sort_die(_("open failed"), output_file);
        }
      else if (nopened <= 2)
        {
          sort_die(_("open failed"), files[nopened].name);
        }

      {
        FILE *tfp;
        struct tempnode *temp;
        do
          {
            nopened--;
            xfclose(fps[nopened], files[nopened].name);
            temp = maybe_create_temp(&tfp, !(nopened <= 2));
          }
        while (!temp);

        {
          size_t limit = min_size_t(ntemps, nopened);
          mergefps(&files[0], limit, nopened, tfp, temp->name, fps);
          ntemps -= limit;
          files[0].name = temp->name;
          files[0].temp = temp;
          if (nfiles > nopened)
            memmove(&files[1], &files[nopened], (nfiles - nopened) * sizeof *files);
          ntemps++;
          nfiles -= nopened - 1;
        }
      }
    }
}

/* Sort NFILES FILES onto OUTPUT_FILE.  Use at most NTHREADS threads.  */

static void
sort (char *const *files, size_t nfiles, char const *output_file,
      size_t nthreads)
{
  struct buffer buf;
  size_t ntemps = 0;
  bool output_file_created = false;

  buf.alloc = 0;

  while (nfiles)
    {
      char const *file = *files;
      FILE *fp = xfopen (file, "r");

      size_t bytes_per_line;
      if (nthreads > 1)
        {
          size_t mult = 1;
          for (size_t tmp = 1; tmp < nthreads; tmp <<= 1)
            mult++;
          bytes_per_line = mult * sizeof (struct line);
        }
      else
        {
          bytes_per_line = sizeof (struct line) * 3 / 2;
        }

      if (! buf.alloc)
        initbuf (&buf, bytes_per_line,
                 sort_buffer_size (&fp, 1, files, nfiles, bytes_per_line));
      buf.eof = false;
      files++;
      nfiles--;

      while (fillbuf (&buf, fp, file))
        {
          if (buf.eof && nfiles
              && (bytes_per_line + 1
                  < (buf.alloc - buf.used - bytes_per_line * buf.nlines)))
            {
              buf.left = buf.used;
              break;
            }

          saved_line.text = NULL;
          struct line *line = buffer_linelim (&buf);

          const char *temp_output;
          FILE *tfp;

          if (buf.eof && !nfiles && !ntemps && !buf.left)
            {
              xfclose (fp, file);
              tfp = xfopen (output_file, "w");
              temp_output = output_file;
              output_file_created = true;
            }
          else
            {
              ++ntemps;
              temp_output = create_temp (&tfp)->name;
            }

          if (1 < buf.nlines)
            {
              struct merge_node_queue queue;
              queue_init (&queue, nthreads);
              struct merge_node *merge_tree =
                merge_tree_init (nthreads, buf.nlines, line);

              sortlines (line, nthreads, buf.nlines, merge_tree + 1,
                         &queue, tfp, temp_output);

              merge_tree_destroy (nthreads, merge_tree);
              queue_destroy (&queue);
            }
          else
            {
              write_unique (line - 1, tfp, temp_output);
            }

          xfclose (tfp, temp_output);

          if (output_file_created)
            break;
        }

      if (output_file_created)
        break;

      xfclose (fp, file);
    }

  free (buf.buf);

  if (! output_file_created)
    {
      struct tempnode *node = temphead;
      struct sortfile *tempfiles = xnmalloc (ntemps, sizeof *tempfiles);
      for (size_t i = 0; node && i < ntemps; i++)
        {
          tempfiles[i].name = node->name;
          tempfiles[i].temp = node;
          node = node->next;
        }
      merge (tempfiles, ntemps, ntemps, output_file);
      free (tempfiles);
    }

  reap_all ();
}

/* Insert a malloc'd copy of key KEY_ARG at the end of the key list.  */

static void insertkey(struct keyfield *key_arg)
{
    struct keyfield **current;
    struct keyfield *new_key;

    if (key_arg == NULL) {
        return;
    }

    new_key = xmemdup(key_arg, sizeof *new_key);
    if (new_key == NULL) {
        return;
    }

    new_key->next = NULL;

    current = &keylist;
    while (*current != NULL) {
        current = &(*current)->next;
    }

    *current = new_key;
}

/* Report a bad field specification SPEC, with extra info MSGID.  */

static void
badfieldspec (char const *spec, char const *msgid)
{
  char const *safe_msg = msgid ? _(msgid) : "";
  char const *safe_spec = quote (spec ? spec : "(null)");

  error (SORT_FAILURE, 0, _("%s: invalid field specification %s"),
         safe_msg, safe_spec);
}

/* Report incompatible options.  */

static void
incompatible_options (char const *opts)
{
  const char *safe_opts = opts ? opts : "";
  error (SORT_FAILURE, 0, _("options '-%s' are incompatible"), safe_opts);
}

/* Check compatibility of ordering options.  */

static void
check_ordering_compatibility(void)
{
  for (struct keyfield *key = keylist; key != NULL; key = key->next)
  {
    int order_flags_count = 0;

    order_flags_count += (key->numeric != 0);
    order_flags_count += (key->general_numeric != 0);
    order_flags_count += (key->human_numeric != 0);
    order_flags_count += (key->month != 0);
    order_flags_count += ((key->version != 0) || (key->random != 0) || (key->ignore != 0));

    if (order_flags_count > 1)
    {
      char opts[sizeof short_options];
      key->skipsblanks = false;
      key->skipeblanks = false;
      key->reverse = false;
      key_to_opts(key, opts);
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
  char *suffix = NULL;
  uintmax_t n = 0;
  int status = xstrtoumax (string, &suffix, 10, &n, "");

  if (status == LONGINT_INVALID)
    {
      if (msgid)
        error (SORT_FAILURE, 0, _("%s: invalid count at start of %s"),
               _(msgid), quote (string));
      return NULL;
    }

  if (status & LONGINT_OVERFLOW)
    {
      *val = SIZE_MAX;
    }
  else
    {
      if (n <= SIZE_MAX)
        *val = (size_t) n;
      else
        *val = SIZE_MAX;
    }

  return suffix;
}

/* Handle interrupts and hangups. */

static void
sighandler (int sig)
{
  struct sigaction sa;

  if (! SA_NOCLDSTOP)
    {
      sigemptyset (&sa.sa_mask);
      sa.sa_flags = 0;
      sa.sa_handler = SIG_IGN;
      (void) sigaction (sig, &sa, NULL);
    }

  cleanup ();

  sigemptyset (&sa.sa_mask);
  sa.sa_flags = 0;
  sa.sa_handler = SIG_DFL;
  (void) sigaction (sig, &sa, NULL);

  (void) kill (getpid (), sig);
}

/* Set the ordering options for KEY specified in S.
   Return the address of the first character in S that
   is not a valid ordering option.
   BLANKTYPE is the kind of blanks that 'b' should skip. */

static char *
set_ordering(const char *s, struct keyfield *key, enum blanktype blanktype)
{
  if (!s || !key)
    return (char *) s;

  const bool set_start_blanks = (blanktype == bl_start) || (blanktype == bl_both);
  const bool set_end_blanks = (blanktype == bl_end) || (blanktype == bl_both);

  for (; *s; s++)
    {
      switch (*s)
        {
        case 'b':
          if (set_start_blanks)
            key->skipsblanks = true;
          if (set_end_blanks)
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
          return (char *) s;
        }
    }
  return (char *) s;
}

/* Initialize KEY.  */

static struct keyfield *
key_init(struct keyfield *key)
{
  if (key == NULL) {
    return NULL;
  }
  memset(key, 0, sizeof(*key));
  key->eword = SIZE_MAX;
  return key;
}

int main (int argc, char **argv)
{
  struct keyfield *key;
  struct keyfield key_buf;
  struct keyfield gkey;
  bool gkey_only = false;
  char const *s;
  int c = 0;
  char checkonly = 0;
  bool mergeonly = false;
  char *random_source = NULL;
  bool need_random = false;
  size_t nthreads = 0;
  size_t nfiles = 0;
  bool posixly_correct = (getenv ("POSIXLY_CORRECT") != NULL);
  int posix_ver = posix2_version ();
  bool traditional_usage = ! (200112 <= posix_ver && posix_ver < 200809);
  char **files;
  char *files_from = NULL;
  struct Tokens tok;
  char const *outfile = NULL;
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

  have_read_stdin = false;
  inittables ();

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
  }
  signal (SIGCHLD, SIG_DFL);

  atexit (exit_cleanup);

  key_init (&gkey);
  gkey.sword = SIZE_MAX;

  files = xnmalloc (argc, sizeof *files);

  while (1)
    {
      int oi = -1;

      if (c == -1
          || (posixly_correct && nfiles != 0
              && ! (traditional_usage
                    && ! checkonly
                    && optind != argc
                    && argv[optind][0] == '-' && argv[optind][1] == 'o'
                    && (argv[optind][2] || optind + 1 != argc)))
          || ((c = getopt_long (argc, argv, short_options,
                                long_options, &oi))
              == -1))
        {
          if (argc <= optind)
            break;
          files[nfiles++] = argv[optind++];
        }
      else switch (c)
        {
        case 1:
          key = NULL;
          if (optarg[0] == '+')
            {
              bool minus_pos_usage = (optind != argc && argv[optind][0] == '-'
                                      && c_isdigit (argv[optind][1]));
              traditional_usage |= minus_pos_usage && !posixly_correct;
              if (traditional_usage)
                {
                  key = key_init (&key_buf);
                  s = parse_field_count (optarg + 1, &key->sword, NULL);
                  if (s && *s == '.')
                    s = parse_field_count (s + 1, &key->schar, NULL);
                  if (! (key->sword || key->schar))
                    key->sword = SIZE_MAX;
                  if (! s || *set_ordering (s, key, bl_start))
                    key = NULL;
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
                            badfieldspec (optarg1,
                                      N_("stray character in field spec"));
                        }
                      key->traditional_used = true;
                      insertkey (key);
                    }
                }
            }
          if (! key)
            files[nfiles++] = optarg;
          break;

        case SORT_OPTION:
          c = XARGMATCH ("--sort", optarg, sort_args, sort_types);
          FALLTHROUGH;
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
          FALLTHROUGH;
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
          key = key_init (&key_buf);

          s = parse_field_count (optarg, &key->sword,
                                 N_("invalid number at field start"));
          if (! key->sword--)
            {
              badfieldspec (optarg, N_("field number is zero"));
            }
          if (*s == '.')
            {
              s = parse_field_count (s + 1, &key->schar,
                                     N_("invalid number after '.'"));
              if (! key->schar--)
                {
                  badfieldspec (optarg, N_("character offset is zero"));
                }
            }
          if (! (key->sword || key->schar))
            key->sword = SIZE_MAX;
          s = set_ordering (s, key, bl_start);
          if (*s != ',')
            {
              key->eword = SIZE_MAX;
              key->echar = 0;
            }
          else
            {
              s = parse_field_count (s + 1, &key->eword,
                                     N_("invalid number after ','"));
              if (! key->eword--)
                {
                  badfieldspec (optarg, N_("field number is zero"));
                }
              if (*s == '.')
                {
                  s = parse_field_count (s + 1, &key->echar,
                                         N_("invalid number after '.'"));
                }
              s = set_ordering (s, key, bl_end);
            }
          if (*s)
            badfieldspec (optarg, N_("stray character in field spec"));
          insertkey (key);
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

        case 's':
          stable = true;
          break;

        case 'S':
          specify_sort_size (oi, c, optarg);
          break;

        case 't':
          {
            char newtab = optarg[0];
            if (! newtab)
              error (SORT_FAILURE, 0, _("empty tab"));
            if (optarg[1])
              {
                if (STREQ (optarg, "\\0"))
                  newtab = '\0';
                else
                  {
                    error (SORT_FAILURE, 0, _("multi-character tab %s"),
                           quote (optarg));
                  }
              }
            if (tab != TAB_DEFAULT && tab != newtab)
              error (SORT_FAILURE, 0, _("incompatible tabs"));
            tab = newtab;
          }
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
    {
      if (nfiles)
        {
          error (0, 0, _("extra operand %s"), quoteaf (files[0]));
          fprintf (stderr, "%s\n",
                   _("file operands cannot be combined with --files0-from"));
          usage (SORT_FAILURE);
        }

      FILE *stream = xfopen (files_from, "r");

      readtokens0_init (&tok);

      if (! readtokens0 (stream, &tok))
        error (SORT_FAILURE, 0, _("cannot read file names from %s"),
               quoteaf (files_from));
      xfclose (stream, files_from);

      if (tok.n_tok)
        {
          free (files);
          files = tok.tok;
          nfiles = tok.n_tok;
          for (size_t i = 0; i < nfiles; i++)
            {
              if (STREQ (files[i], "-"))
                error (SORT_FAILURE, 0, _("when reading file names from "
                                          "standard input, "
                                          "no file name of %s allowed"),
                       quoteaf (files[i]));
              else if (files[i][0] == '\0')
                {
                  unsigned long int file_number = i + 1;
                  error (SORT_FAILURE, 0,
                         _("%s:%lu: invalid zero-length file name"),
                         quotef (files_from), file_number);
                }
            }
        }
      else
        error (SORT_FAILURE, 0, _("no input from %s"),
               quoteaf (files_from));
    }

  for (key = keylist; key; key = key->next)
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
      if (! locale_ok)
          error (0, 0, "%s", _("failed to set locale"));
      if (hard_LC_COLLATE)
        error (0, 0, _("text ordering performed using %s sorting rules"),
               quote (setlocale (LC_COLLATE, NULL)));
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
      add_temp_dir (tmp_dir ? tmp_dir : DEFAULT_TMPDIR);
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
