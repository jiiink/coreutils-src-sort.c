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

#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

static void async_safe_write(int fd, const char *str) {
    ssize_t len = strlen(str);
    while (len > 0) {
        ssize_t written = write(fd, str, len);
        if (written <= 0) return;
        str += written;
        len -= written;
    }
}

static void async_safe_write_int(int fd, int num) {
    char buf[INT_BUFSIZE_BOUND(num)];
    snprintf(buf, sizeof(buf), "%d", num);
    async_safe_write(fd, buf);
}

static _Noreturn void async_safe_die(int errnum, const char *errstr) {
    async_safe_write(STDERR_FILENO, errstr);
    if (errnum) {
        async_safe_write(STDERR_FILENO, ": errno ");
        async_safe_write_int(STDERR_FILENO, errnum);
    }
    async_safe_write(STDERR_FILENO, "\n");
    _exit(EXIT_FAILURE);
}

/* Report MESSAGE for FILE, then clean up and exit.
   If FILE is null, it represents standard output.  */

#include <errno.h>
#include <error.h>

static void sort_die(const char *message, const char *file) {
    const char *output = file ? file : _("standard output");
    error(SORT_FAILURE, errno, "%s: %s", message, quotef(output));
}

#include <stdio.h>
#include <stdlib.h>

void usage(int status) {
    if (status != EXIT_SUCCESS) {
        emit_try_help();
        exit(status);
    }
    
    printf(_("Usage: %s [OPTION]... [FILE]...\n"), program_name);
    printf(_("  or:  %s [OPTION]... --files0-from=F\n"), program_name);
    fputs(_("Write sorted concatenation of all FILE(s) to standard output.\n"), stdout);

    emit_stdin_note();
    emit_mandatory_arg_note();

    fputs(_("Ordering options:\n\n"), stdout);
    fputs(_("  -b, --ignore-leading-blanks  ignore leading blanks\n"), stdout);
    fputs(_("  -d, --dictionary-order      consider only blanks and alphanumeric characters\n"), stdout);
    fputs(_("  -f, --ignore-case           fold lower case to upper case characters\n"), stdout);
    fputs(_("  -g, --general-numeric-sort  compare according to general numerical value\n"), stdout);
    fputs(_("  -i, --ignore-nonprinting    consider only printable characters\n"), stdout);
    fputs(_("  -M, --month-sort            compare (unknown) < 'JAN' < ... < 'DEC'\n"), stdout);
    fputs(_("  -h, --human-numeric-sort    compare human readable numbers (e.g., 2K 1G)\n"), stdout);
    fputs(_("  -n, --numeric-sort          compare according to string numerical value;\n"), stdout);
    fputs(_("                               see full documentation for supported strings\n"), stdout);
    fputs(_("  -R, --random-sort           shuffle, but group identical keys.  See shuf(1)\n"), stdout);
    fputs(_("      --random-source=FILE    get random bytes from FILE\n"), stdout);
    fputs(_("  -r, --reverse               reverse the result of comparisons\n"), stdout);
    fputs(_("      --sort=WORD             sort according to WORD:\n"), stdout);
    fputs(_("                                general-numeric -g, human-numeric -h, month -M,\n"), stdout);
    fputs(_("                                numeric -n, random -R, version -V\n"), stdout);
    fputs(_("  -V, --version-sort          natural sort of (version) numbers within text\n\n"), stdout);

    fputs(_("Other options:\n\n"), stdout);
    fputs(_("      --batch-size=NMERGE   merge at most NMERGE inputs at once;\n"), stdout);
    fputs(_("                            for more use temp files\n"), stdout);
    fputs(_("  -c, --check, --check=diagnose-first  check for sorted input; do not sort\n"), stdout);
    fputs(_("  -C, --check=quiet, --check=silent  like -c, but do not report first bad line\n"), stdout);
    fputs(_("      --compress-program=PROG  compress temporaries with PROG;\n"), stdout);
    fputs(_("                              decompress them with PROG -d\n"), stdout);
    fputs(_("      --debug               annotate the part of the line used to sort, and\n"), stdout);
    fputs(_("                              warn about questionable usage to standard error\n"), stdout);
    fputs(_("      --files0-from=F       read input from the files specified by\n"), stdout);
    fputs(_("                            NUL-terminated names in file F;\n"), stdout);
    fputs(_("                            If F is - then read names from standard input\n"), stdout);
    fputs(_("  -k, --key=KEYDEF          sort via a key; KEYDEF gives location and type\n"), stdout);
    fputs(_("  -m, --merge               merge already sorted files; do not sort\n"), stdout);
    fputs(_("  -o, --output=FILE         write result to FILE instead of standard output\n"), stdout);
    fputs(_("  -s, --stable              stabilize sort by disabling last-resort comparison\n"), stdout);
    fputs(_("  -S, --buffer-size=SIZE    use SIZE for main memory buffer\n"), stdout);

    printf(_("  -t, --field-separator=SEP  use SEP instead of non-blank to blank transition\n"));
    printf(_("  -T, --temporary-directory=DIR  use DIR for temporaries, not $TMPDIR or %s;\n"), DEFAULT_TMPDIR);
    fputs(_("                              multiple options specify multiple directories\n"), stdout);
    fputs(_("      --parallel=N          change the number of sorts run concurrently to N\n"), stdout);
    fputs(_("  -u, --unique              output only the first of lines with equal keys;\n"), stdout);
    fputs(_("                              with -c, check for strict ordering\n"), stdout);
    fputs(_("  -z, --zero-terminated     line delimiter is NUL, not newline\n"), stdout);
    
    fputs(HELP_OPTION_DESCRIPTION, stdout);
    fputs(VERSION_OPTION_DESCRIPTION, stdout);
    fputs(_("\nKEYDEF is F[.C][OPTS][,F[.C][OPTS]] for start and stop position,\n"), stdout);
    fputs(_("where F is a field number and C a character position in the field; both are origin 1,\n"), stdout);
    fputs(_("and the stop position defaults to the line's end.\n"), stdout);
    fputs(_("If neither -t nor -b is in effect, characters in a field are counted from the beginning\n"), stdout);
    fputs(_("of the preceding whitespace.\n"), stdout);
    fputs(_("OPTS is one or more single-letter ordering options [bdfgiMhnRrV],\n"), stdout);
    fputs(_("which override global ordering options for that key.\n"), stdout);
    fputs(_("If no key is given, use the entire line as the key. Use --debug to diagnose incorrect key usage.\n\n"), stdout);
    fputs(_("SIZE may be followed by the following multiplicative suffixes:\n"), stdout);
    fputs(_("% 1% of memory, b 1, K 1024 (default), and so on for M, G, T, P, E, Z, Y, R, Q.\n"), stdout);
    fputs(_("\n*** WARNING ***\nThe locale specified by the environment affects sort order.\n"), stdout);
    fputs(_("Set LC_ALL=C to get the traditional sort order that uses\nnative byte values.\n"), stdout);
    
    emit_ancillary_info(PROGRAM_NAME);
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
#include <pthread.h>
#include <string.h>

static void cs_enter(struct cs_status *status) {
    if (status == NULL) {
        return;
    }

    int ret = pthread_sigmask(SIG_BLOCK, &caught_signals, &status->sigs);
    status->valid = (ret == 0);
    if (ret != 0) {
        memset(&status->sigs, 0, sizeof(status->sigs));
    }
}

/* Leave a critical section.  */
static void cs_leave(const struct cs_status *status) {
    if (status && status->valid) {
        int ret = pthread_sigmask(SIG_SETMASK, &status->sigs, NULL);
        if (ret != 0) {
            // Handle error as appropriate, possibly logging or returning an error code.
        }
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

#include <stddef.h>

static size_t proctab_hasher(const void *entry, size_t tabsize) {
    if (entry == NULL || tabsize == 0) {
        return 0;
    }
    const struct tempnode *node = entry;
    return node->pid % tabsize;
}

static int proctab_comparator(const void *e1, const void *e2) {
    const struct tempnode *n1 = e1;
    const struct tempnode *n2 = e2;
    return (n1->pid > n2->pid) - (n1->pid < n2->pid);
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

#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>

static pid_t reap(pid_t pid) {
    int status;
    pid_t cpid = waitpid(pid, &status, pid ? 0 : WNOHANG);

    if (cpid < 0) {
        error(SORT_FAILURE, errno, _("waiting for %s [-d]"), quoteaf(compress_program));
        return cpid;
    }

    if (cpid > 0 && (pid > 0 || delete_proc(cpid))) {
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
            error(SORT_FAILURE, 0, _("%s [-d] terminated abnormally"), quoteaf(compress_program));
        } else {
            --nprocs;
        }
    }

    return cpid;
}

/* TEMP represents a new process; add it to the process table.  Create
   the process table the first time it's called.  */

static void register_proc(struct tempnode *temp) {
    if (!proctab) {
        proctab = hash_initialize(INIT_PROCTAB_SIZE, NULL,
                                  proctab_hasher, proctab_comparator, NULL);
        if (!proctab) {
            xalloc_die();
        }
    }

    temp->state = UNREAPED;

    if (!hash_insert(proctab, temp)) {
        xalloc_die();
    }
}

/* If PID is in the process table, remove it and return true.
   Otherwise, return false.  */

#include <stdbool.h>
#include <stddef.h>

typedef struct {
  pid_t pid;
  int state;
} tempnode;

#define REAPED 1

tempnode* hash_remove(void* hash_table, tempnode* node);

bool delete_proc(pid_t pid) {
  tempnode test;
  test.pid = pid;

  tempnode *node = hash_remove(proctab, &test);

  if (node == NULL) {
    return false;
  }

  node->state = REAPED;
  return true;
}

/* Remove PID from the process table, and wait for it to exit if it
   hasn't already.  */

#include <stdbool.h>

static void handle_process(pid_t pid) {
    if (delete_proc(pid)) {
        reap(pid);
    }
}

/* Reap any exited children.  Do not block; reap only those that have
   already exited.  */

static void reap_exited(void) {
    while (nprocs > 0 && reap(0)) {
        nprocs--;  // Assuming nprocs decrement would be meaningful in context
    }
}

/* Reap at least one exited child, waiting if necessary.  */

static void reap_some(void) {
    if (reap(-1) != 0) {
        // Handle error appropriately, e.g., log or return
        return;
    }
    reap_exited();
}

/* Reap all children, waiting if necessary.  */

static void reap_all(void) {
    while (nprocs > 0) {
        reap(-1);
    }
}

/* Clean up any remaining temporary files.  */

#include <errno.h>
#include <stdio.h>

static void cleanup(void) {
    struct tempnode const *node = temphead;

    while (node != NULL) {
        if (unlink(node->name) != 0) {
            fprintf(stderr, "Error unlinking %s: %s\n", node->name, strerror(errno));
        }
        node = node->next;
    }
    temphead = NULL;
}

/* Cleanup actions to take when exiting.  */

#include <signal.h>
#include <stdbool.h>

static volatile sig_atomic_t is_cleanup_in_progress = false;

static void exit_cleanup(void) {
    if (temphead) {
        if (__sync_bool_compare_and_swap(&is_cleanup_in_progress, false, true)) {
            struct cs_status cs;
            cs_enter(&cs);
            cleanup();
            cs_leave(&cs);
            is_cleanup_in_progress = false;
        }
    }
    close_stdout();
}

/* Create a new temporary file, returning its newly allocated tempnode.
   Store into *PFD the file descriptor open for writing.
   If the creation fails, return nullptr and store -1 into *PFD if the
   failure is due to file descriptor exhaustion and
   SURVIVE_FD_EXHAUSTION; otherwise, die.  */

#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

struct tempnode {
    struct tempnode *next;
    char name[];
};

static struct tempnode **temptail;
static int temp_dir_count;
static const char *temp_dirs[];
void cs_enter(struct cs_status *cs);
void cs_leave(struct cs_status *cs);
void error(int status, int errnum, const char *format, ...);
char *quoteaf(const char *str);
void *xmalloc(size_t size);

static struct tempnode *create_temp_file(int *pfd, bool survive_fd_exhaustion) {
    static const char slashbase[] = "/sortXXXXXX";
    static idx_t temp_dir_index;
    struct tempnode *node = NULL;
    char *file;
    struct cs_status cs;
    char const *temp_dir = temp_dirs[temp_dir_index];
    size_t len = strlen(temp_dir);

    node = xmalloc(sizeof(*node) + len + sizeof(slashbase));
    if (!node) {
        *pfd = -1;
        return NULL;
    }

    file = node->name;
    memcpy(file, temp_dir, len);
    memcpy(file + len, slashbase, sizeof(slashbase));

    node->next = NULL;
    temp_dir_index = (temp_dir_index + 1) % temp_dir_count;

    cs_enter(&cs);
    int fd = mkostemp(file, O_CLOEXEC);
    int saved_errno = errno;
    cs_leave(&cs);
    errno = saved_errno;

    if (fd >= 0) {
        *temptail = node;
        temptail = &node->next;
    } else {
        if (!survive_fd_exhaustion || errno != EMFILE) {
            error(SORT_FAILURE, errno, "cannot create temporary file in %s", quoteaf(temp_dir));
        }
        free(node);
        node = NULL;
    }

    *pfd = fd;
    return node;
}

/* Return a pointer to stdout status, or nullptr on failure.  */

#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

static struct stat *get_outstatus(void) {
    static int outstat_errno = 0;
    static struct stat outstat;
    
    if (outstat_errno == 0) {
        if (fstat(STDOUT_FILENO, &outstat) == 0) {
            outstat_errno = -1;
        } else {
            outstat_errno = errno;
        }
    }
    
    return (outstat_errno == -1) ? &outstat : NULL;
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

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/stat.h>

static FILE *stream_open(const char *file, const char *how) {
    if (!file || !how) return NULL;

    FILE *fp = NULL;
    if (*how == 'r' && STREQ(file, "-")) {
        have_read_stdin = true;
        fp = stdin;
        fadvise(fp, FADVISE_SEQUENTIAL);
    } else if (*how == 'r') {
        int fd = open(file, O_RDONLY | O_CLOEXEC);
        if (fd >= 0) {
            fp = fdopen(fd, how);
            fadvise(fp, FADVISE_SEQUENTIAL);
        }
    } else if (*how == 'w') {
        if (ftruncate(STDOUT_FILENO, 0) != 0) {
            int ftruncate_errno = errno;
            struct stat *outst = get_outstatus();
            if (!outst || S_ISREG(outst->st_mode) || S_TYPEISSHM(outst)) {
                error(SORT_FAILURE, ftruncate_errno, _("%s: error truncating"), quotef(file));
            }
        }
        fp = stdout;
    }

    return fp;
}

/* Same as stream_open, except always return a non-null value; die on
   failure.  */

#include <stdio.h>
#include <stdlib.h>

static FILE *xfopen(const char *file, const char *how) {
  FILE *fp = fopen(file, how);
  if (!fp) {
    perror("Failed to open file");
    exit(EXIT_FAILURE);
  }
  return fp;
}

/* Close FP, whose name is FILE, and report any errors.  */

#include <stdio.h>
#include <unistd.h>

static void handle_close_error(const char *message, const char *file) {
  fprintf(stderr, "%s: %s\n", message, file);
  exit(EXIT_FAILURE);
}

static void xfclose(FILE *fp, const char *file) {
  int fd = fileno(fp);
  if (fd == -1) {
    handle_close_error("Invalid file descriptor", file);
  }

  if (fd == STDIN_FILENO) {
    clearerr(fp);
  } else if (fd == STDOUT_FILENO) {
    if (fflush(fp) != 0) {
      handle_close_error("fflush failed", file);
    }
  } else {
    if (fclose(fp) != 0) {
      handle_close_error("close failed", file);
    }
  }
}

/* Move OLDFD to NEWFD.  If OLDFD != NEWFD, NEWFD is not close-on-exec.  */

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>

static void handle_error(const char *message) {
    perror(message);
    exit(EXIT_FAILURE);
}

static void move_fd(int oldfd, int newfd) {
    if (oldfd != newfd) {
        if (dup2(oldfd, newfd) == -1) {
            handle_error("dup2 failed");
        }
        if (close(oldfd) == -1) {
            handle_error("close failed");
        }
    }
}

/* Fork a child process for piping to and do common cleanup.  The
   TRIES parameter specifies how many times to try to fork before
   giving up.  Return the PID of the child, or -1 (setting errno)
   on failure. */

#include <errno.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

#define RETRY_SLEEP_TIME 0.25
#define TEMP_HEAD_NULL nullptr

static pid_t pipe_fork(int pipefds[2], size_t tries) {
#if HAVE_WORKING_FORK
    pid_t pid = -1;
    struct cs_status cs;
    struct tempnode *saved_temphead = TEMP_HEAD_NULL;

    if (pipe2(pipefds, O_CLOEXEC) < 0) {
        return -1;
    }

    if (nmerge + 1 < nprocs) {
        reap_some();
    }

    while (tries-- > 0) {
        int saved_errno;

        cs_enter(&cs);
        saved_temphead = temphead;
        temphead = TEMP_HEAD_NULL;

        pid = fork();
        saved_errno = errno;
        temphead = saved_temphead;
        cs_leave(&cs);

        if (pid >= 0) {
            errno = saved_errno;
            break;
        } else if (errno != EAGAIN) {
            errno = saved_errno;
            break;
        }

        xnanosleep(RETRY_SLEEP_TIME * (1 << (tries & 3)));
        reap_exited();
    }

    if (pid < 0) {
        close(pipefds[0]);
        close(pipefds[1]);
    } else if (pid == 0) {
        close(STDIN_FILENO);
        close(STDOUT_FILENO);
    } else {
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

#include <errno.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>

static struct tempnode *maybe_create_temp(FILE **pfp, bool survive_fd_exhaustion) {
    int tempfd;
    struct tempnode *node = create_temp_file(&tempfd, survive_fd_exhaustion);
    if (!node) return NULL;

    node->state = UNCOMPRESSED;

    if (compress_program) {
        int pipefds[2];
        
        node->pid = pipe_fork(pipefds, MAX_FORK_TRIES_COMPRESS);
        if (node->pid > 0) {
            close(tempfd);
            close(pipefds[0]);
            tempfd = pipefds[1];
            register_proc(node);
        } else if (node->pid == 0) {
            close(pipefds[1]);
            move_fd(tempfd, STDOUT_FILENO);
            move_fd(pipefds[0], STDIN_FILENO);
            execlp(compress_program, compress_program, NULL);
            async_safe_die(errno, "couldn't execute compress program");
        }
    }

    *pfp = fdopen(tempfd, "w");
    if (!*pfp) sort_die("couldn't create temporary file", node->name);

    return node;
}

/* Create a temporary file and, if asked for, start a compressor
   to that file.  Set *PFP to the file handle and return the address
   of the new temp node.  Die on failure.  */

#include <stdio.h>

static struct tempnode *create_temp(FILE **pfp) {
    if (pfp == NULL) {
        return NULL;
    }
    return maybe_create_temp(pfp, false);
}

/* Open a compressed temp file and start a decompression process through
   which to filter the input.  Return nullptr (setting errno to
   EMFILE) if we ran out of file descriptors, and die on any other
   kind of failure.  */

#include <fcntl.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>

static FILE *open_temp(struct tempnode *temp)
{
    if (temp->state == UNREAPED)
    {
        wait_proc(temp->pid);
    }

    int tempfd = open(temp->name, O_RDONLY);
    if (tempfd < 0)
    {
        return NULL;
    }

    int pipefds[2];
    pid_t child = pipe_fork(pipefds, MAX_FORK_TRIES_DECOMPRESS);
    if (child == -1)
    {
        if (errno != EMFILE)
        {
            error(SORT_FAILURE, errno, _("couldn't create process for %s -d"), quoteaf(compress_program));
        }
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

    FILE *fp = fdopen(pipefds[0], "r");
    if (!fp)
    {
        int saved_errno = errno;
        close(pipefds[0]);
        errno = saved_errno;
    }

    return fp;
}

/* Append DIR to the array of temporary directory names.  */
#include <errno.h>
#include <stdlib.h>

static void add_temp_dir(const char *dir) {
    if (!dir) {
        // Handle the null pointer error, e.g., log or abort based on application
        return;
    }

    if (temp_dir_count == temp_dir_alloc) {
        void *new_dirs = realloc(temp_dirs, (temp_dir_alloc + 1) * sizeof(*temp_dirs));
        if (!new_dirs) {
            // Handle memory allocation error
            abort();
        }
        temp_dirs = new_dirs;
        temp_dir_alloc++;
    }

    temp_dirs[temp_dir_count++] = dir;
}

/* Remove NAME from the list of temporary files.  */

#include <errno.h>
#include <stdlib.h>

static void zaptemp(const char *name) {
  struct tempnode *volatile *pnode = &temphead;
  struct tempnode *node;

  while ((node = *pnode) && node->name != name) {
    pnode = &node->next;
  }

  if (!node) {
    return; // Node not found
  }

  if (node->state == UNREAPED) {
    wait_proc(node->pid);
  }

  struct tempnode *next = node->next;
  struct cs_status cs;
  cs_enter(&cs);

  if (unlink(name) != 0) {
    int unlink_errno = errno;
    error(0, unlink_errno, _("warning: cannot remove: %s"), quotef(name));
  }

  *pnode = next;
  cs_leave(&cs);

  if (!next) {
    temptail = pnode;
  }
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

#include <ctype.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#if HAVE_NL_LANGINFO
#include <langinfo.h>
#endif

#define UCHAR_LIM (UCHAR_MAX + 1)
#define MONTHS_PER_YEAR 12

typedef struct {
  char *name;
  int val;
} Month;

Month monthtab[MONTHS_PER_YEAR];

char blanks[UCHAR_LIM];
char nondictionary[UCHAR_LIM];
char nonprinting[UCHAR_LIM];
char fold_toupper[UCHAR_LIM];

static void inittables(void) {
  for (size_t i = 0; i < UCHAR_LIM; ++i) {
    unsigned char ui = (unsigned char)i;
    blanks[ui] = (ui == '\n' || isblank(ui));
    nondictionary[ui] = !blanks[ui] && !isalnum(ui);
    nonprinting[ui] = !isprint(ui);
    fold_toupper[ui] = toupper(ui);
  }

#if HAVE_NL_LANGINFO
  if (hard_LC_TIME) {
    for (size_t i = 0; i < MONTHS_PER_YEAR; i++) {
      const char *s = nl_langinfo(ABMON_1 + i);
      size_t s_len = strlen(s);
      monthtab[i].name = xmalloc(s_len + 1);
      monthtab[i].val = i + 1;

      char *name = monthtab[i].name;
      size_t k = 0;
      for (size_t j = 0; j < s_len; j++) {
        unsigned char ch = to_uchar(s[j]);
        if (!isblank(ch)) {
          name[k++] = fold_toupper[ch];
        }
      }
      name[k] = '\0';
    }
    qsort(monthtab, MONTHS_PER_YEAR, sizeof(*monthtab), struct_month_cmp);
  }
#endif
}

/* Specify how many inputs may be merged at once.
   This may be set on the command-line with the
   --batch-size option. */
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <unistd.h>

static void specify_nmerge(int oi, char c, const char *s) {
    uintmax_t n;
    struct rlimit rlimit;
    unsigned int max_nmerge = OPEN_MAX - 3;
    
    if (getrlimit(RLIMIT_NOFILE, &rlimit) == 0) {
        max_nmerge = rlimit.rlim_cur - 3;
    }

    enum strtol_error e = xstrtoumax(s, NULL, 10, &n, "");
    if (e != LONGINT_OK) {
        xstrtol_fatal(e, oi, c, long_options, s);
        return;
    }

    if (n < 2 || n > max_nmerge) {
        if (n < 2) {
            error(0, 0, _("invalid --%s argument %s"), long_options[oi].name, quote(s));
            error(SORT_FAILURE, 0, _("minimum --%s argument is 2"), long_options[oi].name);
        } else {
            error(0, 0, _("--%s argument %s too large"), long_options[oi].name, quote(s));
            error(SORT_FAILURE, 0, _("maximum --%s argument with current rlimit is %u"), long_options[oi].name, max_nmerge);
        }
        return;
    }

    nmerge = n;
}

/* Specify the amount of main memory to use when sorting.  */
static void specify_sort_size(int oi, char c, char const *s) {
    uintmax_t n;
    char *suffix;
    enum strtol_error e = xstrtoumax(s, &suffix, 10, &n, "EgGkKmMPQRtTYZ");

    if (e == LONGINT_OK && c_isdigit(suffix[-1])) {
        if (n <= UINTMAX_MAX / 1024) {
            n *= 1024;
        } else {
            e = LONGINT_OVERFLOW;
        }
    }

    if (e == LONGINT_INVALID_SUFFIX_CHAR && c_isdigit(suffix[-1]) && suffix[1] == '\0') {
        if (suffix[0] == 'b') {
            e = LONGINT_OK;
        } else if (suffix[0] == '%') {
            double mem = physmem_total() * n / 100;
            if (mem < UINTMAX_MAX) {
                n = (uintmax_t)mem;
                e = LONGINT_OK;
            } else {
                e = LONGINT_OVERFLOW;
            }
        }
    }

    if (e == LONGINT_OK) {
        if (n >= sort_size) {
            sort_size = MAX(n, MIN_SORT_SIZE);
            return;
        }
    }

    xstrtol_fatal(e, oi, c, long_options, s);
}

/* Specify the number of threads to spawn during internal sort.  */
#include <errno.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

static size_t specify_nthreads(int oi, char c, const char *s) {
  uintmax_t nthreads;
  enum strtol_error e = xstrtoumax(s, NULL, 10, &nthreads, "");

  if (e != LONGINT_OK) {
    if (e == LONGINT_OVERFLOW || SIZE_MAX < nthreads) {
      return SIZE_MAX;
    } else {
      xstrtol_fatal(e, oi, c, long_options, s);
    }
  }

  if (nthreads == 0) {
    error(SORT_FAILURE, 0, _("number in parallel must be nonzero"));
  }

  return (size_t)nthreads;
}

/* Return the default sort size.  */
#include <limits.h>
#include <sys/resource.h>

#define MIN_SORT_SIZE 1024

static size_t get_minimum_resource_limit(int resource) {
    struct rlimit rlimit;
    if (getrlimit(resource, &rlimit) == 0) {
        return rlimit.rlim_cur;
    }
    return SIZE_MAX;
}

static double get_max(double a, double b) {
    return (a > b) ? a : b;
}

static size_t get_physical_memory_limit(double avail, double total) {
    double mem = get_max(avail, total / 8);
    size_t mem_limit = (size_t)(total * 0.75);
    return (mem < mem_limit) ? (size_t)mem : mem_limit;
}

static size_t default_sort_size(void) {
    size_t size = SIZE_MAX;
    size = get_minimum_resource_limit(RLIMIT_DATA) < size ? get_minimum_resource_limit(RLIMIT_DATA) : size;
#ifdef RLIMIT_AS
    size = get_minimum_resource_limit(RLIMIT_AS) < size ? get_minimum_resource_limit(RLIMIT_AS) : size;
#endif
    size /= 2;
#ifdef RLIMIT_RSS
    struct rlimit rlimit;
    if (getrlimit(RLIMIT_RSS, &rlimit) == 0) {
        size_t rss_limit = rlimit.rlim_cur / 16 * 15;
        size = rss_limit < size ? rss_limit : size;
    }
#endif

    double avail = physmem_available();
    double total = physmem_total();
    size_t mem_limit = get_physical_memory_limit(avail, total);

    size = mem_limit < size ? mem_limit : size;
    return size > MIN_SORT_SIZE ? size : MIN_SORT_SIZE;
}

/* Return the sort buffer size to use with the input files identified
   by FPS and FILES, which are alternate names of the same files.
   NFILES gives the number of input files; NFPS may be less.  Assume
   that each input line requires LINE_BYTES extra bytes' worth of line
   information.  Do not exceed the size bound specified by the user
   (or a default size bound, if the user does not specify one).  */

#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

static size_t calculate_file_size(const char *file, FILE *file_pointer) {
    struct stat st;
    if ((file_pointer ? fstat(fileno(file_pointer), &st) : stat(file, &st)) != 0) return (size_t)-1;
    return (usable_st_size(&st) && st.st_size > 0) ? st.st_size : INPUT_FILE_SIZE_GUESS;
}

static size_t sort_buffer_size(FILE *const *fps, size_t nfps, char *const *files, size_t nfiles, size_t line_bytes) {
    static size_t size_bound;
    size_t worst_case_per_input_byte = line_bytes + 1;
    size_t total_size = worst_case_per_input_byte + 1;

    for (size_t i = 0; i < nfiles; i++) {
        size_t file_size = i < nfps ? calculate_file_size(NULL, fps[i]) : calculate_file_size(files[i], NULL);
        if (file_size == (size_t)-1) sort_die(_("stat failed"), files[i]);

        if (!size_bound) size_bound = sort_size ? sort_size : default_sort_size();

        size_t worst_case = file_size * worst_case_per_input_byte + 1;
        if (file_size != worst_case / worst_case_per_input_byte || size_bound - total_size <= worst_case) return size_bound;
        total_size += worst_case;
    }

    return total_size;
}

/* Initialize BUF.  Reserve LINE_BYTES bytes for each line; LINE_BYTES
   must be at least sizeof (struct line).  Allocate ALLOC bytes
   initially.  */

#include <stdlib.h>
#include <stdbool.h>

static void handle_allocation_failure(size_t alloc) {
    if (alloc <= 0) {
        // This function should handle critical allocation failures
        // e.g., logging the error, cleaning up resources, etc.
        exit(EXIT_FAILURE);
    }
}

static void *try_allocate(size_t size) {
    void *ptr = malloc(size);
    return ptr;
}

static void initbuf(struct buffer *buf, size_t line_bytes, size_t initial_alloc) {
    size_t alloc = initial_alloc;
    
    do {
        alloc += sizeof(struct line) - alloc % sizeof(struct line);
        buf->buf = try_allocate(alloc);
        
        if (buf->buf == NULL) {
            alloc /= 2;
            handle_allocation_failure(alloc - line_bytes - 1);
        }
    } while (buf->buf == NULL);

    buf->line_bytes = line_bytes;
    buf->alloc = alloc;
    buf->used = 0;
    buf->left = 0;
    buf->nlines = 0;
    buf->eof = false;
}

/* Return one past the limit of the line array.  */

static inline struct line *buffer_linelim(const struct buffer *buf) {
    if (buf == NULL) {
        return NULL;
    }
    return (struct line *)((char *)buf->buf + buf->alloc);
}

/* Return a pointer to the first character of the field specified
   by KEY in LINE. */

static char *begfield(struct line const *line, struct keyfield const *key) {
    char *ptr = line->text;
    char *lim = ptr + line->length - 1;
    size_t sword = key->sword;
    size_t schar = key->schar;

    while (ptr < lim && sword > 0) {
        if (tab != TAB_DEFAULT) {
            while (ptr < lim && *ptr != tab) ++ptr;
        } else {
            while (ptr < lim && blanks[to_uchar(*ptr)]) ++ptr;
            while (ptr < lim && !blanks[to_uchar(*ptr)]) ++ptr;
        }
        
        if (ptr < lim) ++ptr;
        sword--;
    }

    if (key->skipsblanks) {
        while (ptr < lim && blanks[to_uchar(*ptr)]) ++ptr;
    }

    ptr += (schar < (size_t)(lim - ptr)) ? schar : (lim - ptr);

    return ptr;
}

/* Return the limit of (a pointer to the first character after) the field
   in LINE specified by KEY. */

ATTRIBUTE_PURE
static char *
limfield(struct line const *line, struct keyfield const *key) {
    char *ptr = line->text, *lim = ptr + line->length - 1;
    size_t eword = key->eword, echar = key->echar;
    echar = (echar == 0) ? eword++ : echar;

    size_t (*is_tab_or_blank)(unsigned char) = (tab != TAB_DEFAULT) ? 
        (size_t (*)(unsigned char)) (unsigned char c) { return c == tab; }:
        (size_t (*)(unsigned char)) (unsigned char c) { return blanks[c]; };

    while (ptr < lim && eword--) {
        while (ptr < lim && !is_tab_or_blank(to_uchar(*ptr)))
            ++ptr;
        while (ptr < lim && (eword || echar) && is_tab_or_blank(to_uchar(*ptr)))
            ++ptr;
    }
    
    if (echar) {
        if (key->skipeblanks)
            while (ptr < lim && blanks[to_uchar(*ptr)])
                ++ptr;

        ptr += (echar < (size_t)(lim - ptr)) ? echar : (size_t)(lim - ptr);
    }

    return ptr;
}

/* Fill BUF reading from FP, moving buf->left bytes from the end
   of buf->buf to the beginning first.  If EOF is reached and the
   file wasn't terminated by a newline, supply one.  Set up BUF's line
   table too.  FILE is the name of the file corresponding to FP.
   Return true if some input was read.  */

#include <stdio.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static bool fill_buffer(struct buffer *buf, FILE *fp, const char *file) {
    const struct keyfield *key = keylist;
    char eol = eolchar;
    size_t line_bytes = buf->line_bytes;
    size_t mergesize = merge_buffer_size - MIN_MERGE_BUFFER_SIZE;

    if (buf->eof)
        return false;

    if (buf->used != buf->left) {
        memmove(buf->buf, buf->buf + buf->used - buf->left, buf->left);
        buf->used = buf->left;
        buf->nlines = 0;
    }

    while (true) {
        char *ptr = buf->buf + buf->used;
        struct line *linelim = buffer_linelim(buf);
        struct line *line = linelim - buf->nlines;
        size_t avail = (char *)linelim - buf->nlines * line_bytes - ptr;
        char *line_start = buf->nlines ? line->text + line->length : buf->buf;

        while (line_bytes + 1 < avail) {
            size_t readsize = (avail - 1) / (line_bytes + 1);
            size_t bytes_read = fread(ptr, 1, readsize, fp);
            if (ferror(fp)) {
                sort_die("read failed", file);
            }
            if (bytes_read != readsize && feof(fp)) {
                buf->eof = true;
                if (buf->buf == ptr + bytes_read) return false;
                if (line_start != ptr + bytes_read && ptr[bytes_read - 1] != eol) {
                    ptr[bytes_read++] = eol;
                }
            }

            char *p;
            while ((p = memchr(ptr, eol, ptr + bytes_read - ptr))) {
                *p = '\0';
                ptr = p + 1;
                line--;
                line->text = line_start;
                line->length = ptr - line_start;
                mergesize = (mergesize > line->length) ? mergesize : line->length;

                if (key) {
                    line->keylim = (key->eword == SIZE_MAX) ? p : limfield(line, key);

                    if (key->sword != SIZE_MAX) {
                        line->keybeg = begfield(line, key);
                    } else {
                        if (key->skipsblanks) {
                            while (blanks[(unsigned char)(*line_start)]) {
                                line_start++;
                            }
                        }
                        line->keybeg = line_start;
                    }
                }
                line_start = ptr;
            }

            ptr += bytes_read;
            if (buf->eof) break;
        }

        buf->used = ptr - buf->buf;
        buf->nlines = buffer_linelim(buf) - line;
        if (buf->nlines > 0) {
            buf->left = ptr - line_start;
            merge_buffer_size = mergesize + MIN_MERGE_BUFFER_SIZE;
            return true;
        }

        idx_t line_alloc = buf->alloc / sizeof(struct line);
        buf->buf = xpalloc(buf->buf, &line_alloc, 1, -1, sizeof(struct line));
        buf->alloc = line_alloc * sizeof(struct line);
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
static char traverse_raw_number(const char **number) {
    const char *p = *number;
    char ch;
    char max_digit = '\0';
    bool ends_with_thousands_sep = false;

    while ((ch = *p) && c_isdigit(ch)) {
        if (max_digit < ch) {
            max_digit = ch;
        }
        ends_with_thousands_sep = (*(++p) == thousands_sep);
        if (ends_with_thousands_sep) {
            p++;
        }
    }

    if (ends_with_thousands_sep && !c_isdigit(*p)) {
        *number = p - 1; 
        return max_digit;
    }

    if (ch == decimal_point) {
        while ((ch = *p) && c_isdigit(ch)) {
            if (max_digit < ch) {
                max_digit = ch;
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
static int find_unit_order(const char *number) {
    if (!number || !*number) return 0;

    bool minus_sign = *number == '-';
    char const *p = number + minus_sign;
    if (!p) return 0;

    char max_digit = traverse_raw_number(&p);
    if (max_digit <= '0') return 0;

    char next_char = *p;
    return minus_sign ? -unit_order[next_char] : unit_order[next_char];
}

/* Compare numbers A and B ending in units with SI or IEC prefixes
       <none/unknown> < K/k < M < G < T < P < E < Z < Y < R < Q */

ATTRIBUTE_PURE
static int
human_numcompare (char const *a, char const *b)
{
  a += strspn(a, blanks);
  b += strspn(b, blanks);

  int diff = find_unit_order(a) - find_unit_order(b);
  if (diff != 0) {
    return diff;
  }
  
  return strnumcmp(a, b, decimal_point, thousands_sep);
}

/* Compare strings A and B as numbers without explicitly converting them to
   machine numbers.  Comparatively slow for short strings, but asymptotically
   hideously fast. */

#include <ctype.h>

ATTRIBUTE_PURE
static int numcompare(const char *a, const char *b) {
    while (*a && isspace((unsigned char)*a)) a++;
    while (*b && isspace((unsigned char)*b)) b++;
    
    return strnumcmp(a, b, decimal_point, thousands_sep);
}

#include <stdio.h>
#include <string.h>
#include <float.h>

static int nan_compare(long double a, long double b) {
    if (isnan(a) && isnan(b)) {
        return 0;
    }
    if (isnan(a)) {
        return 1;
    }
    if (isnan(b)) {
        return -1;
    }
    return (a > b) - (a < b);
}

#include <errno.h>
#include <math.h>
#include <stdlib.h>

static int nan_compare(long double a, long double b);

static int general_numcompare(const char *sa, const char *sb) {
    char *ea;
    char *eb;
    errno = 0;
    long double a = strtold(sa, &ea);
    long double b = strtold(sb, &eb);

    if (errno || sa == ea) {
        return (errno || sb == eb) ? 0 : -1;
    }
    if (sb == eb) {
        return 1;
    }

    if (a == b) {
        return 0;
    }
    if (isnan(a)) {
        return isnan(b) ? nan_compare(a, b) : 1;
    }
    if (isnan(b)) {
        return -1;
    }
    return a < b ? -1 : 1;
}

/* Return an integer in 1..12 of the month name MONTH.
   Return 0 if the name in S is not recognized.  */

static int getmonth(const char *month, char **ea) {
    size_t lo = 0;
    size_t hi = MONTHS_PER_YEAR;

    if (!month) {
        return 0;
    }

    while (*month && blanks[to_uchar(*month)]) {
        month++;
    }
    
    while (lo < hi) {
        size_t ix = (lo + hi) / 2;
        const char *m = month;
        const char *n = monthtab[ix].name;

        while (*n && to_uchar(fold_toupper[to_uchar(*m)]) == to_uchar(*n)) {
            m++;
            n++;
        }
        
        if (!*n) {
            if (ea) {
                *ea = (char *)m;
            }
            return monthtab[ix].val;
        }

        if (to_uchar(fold_toupper[to_uchar(*m)]) < to_uchar(*n)) {
            hi = ix;
        } else {
            lo = ix + 1;
        }
    }

    if (ea) {
        *ea = (char *)month;
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
static void link_libcrypto(void) {
#if DLOPEN_LIBCRYPTO && HAVE_OPENSSL_MD5
    void *handle = dlopen(LIBCRYPTO_SONAME, RTLD_LAZY | RTLD_GLOBAL);
    if (handle == NULL) {
        link_failure();
        return;
    }

    ptr_MD5_Init = symbol_address(handle, "MD5_Init");
    if (ptr_MD5_Init == NULL) {
        link_failure();
        return;
    }

    ptr_MD5_Update = symbol_address(handle, "MD5_Update");
    if (ptr_MD5_Update == NULL) {
        link_failure();
        return;
    }

    ptr_MD5_Final = symbol_address(handle, "MD5_Final");
    if (ptr_MD5_Final == NULL) {
        link_failure();
        return;
    }
#endif
}

/* A randomly chosen MD5 state, used for random comparison.  */
static struct md5_ctx random_md5_state;

/* Initialize the randomly chosen MD5 state.  */

#include <errno.h>

static void random_md5_state_init(const char *random_source) {
    unsigned char buf[MD5_DIGEST_SIZE];
    struct randread_source *r = randread_new(random_source, sizeof buf);
    
    if (!r) {
        sort_die(_("open failed"), random_source ? random_source : "getrandom");
    }

    if (randread(r, buf, sizeof buf) != (int)sizeof buf) {
        randread_free(r);
        sort_die(_("read failed"), random_source);
    }
    
    if (randread_free(r) != 0) {
        sort_die(_("close failed"), random_source);
    }

    link_libcrypto();
    md5_init_ctx(&random_md5_state);
    md5_process_bytes(buf, sizeof buf, &random_md5_state);
}

/* This is like strxfrm, except it reports any error and exits.  */

#include <errno.h>
#include <string.h>
#include <error.h>

static size_t xstrxfrm(char *restrict dest, const char *restrict src, size_t destsize) {
    errno = 0;
    size_t translated_size = strxfrm(dest, src, destsize);

    if (errno != 0) {
        error(0, errno, "string transformation failed");
        error(0, 0, "set LC_ALL='C' to work around the problem");
        error(SORT_FAILURE, 0, "the original string was %s", quotearg_n_style(0, locale_quoting_style, src));
        errno = 0;  // Clear errno after handling
    }

    return translated_size;
}

/* Compare the keys TEXTA (of length LENA) and TEXTB (of length LENB)
   using one or more random hash functions.  TEXTA[LENA] and
   TEXTB[LENB] must be zero.  */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define SIZE_MAX ((size_t)(-1))
#define MD5_DIGEST_SIZE 16

static int compare_random(char *restrict texta, size_t lena, char *restrict textb, size_t lenb) {
    int xfrm_diff = 0;

    char stackbuf[4000];
    char *buf = stackbuf;
    size_t bufsize = sizeof stackbuf;
    char *allocated = NULL;

    uint32_t dig[2][MD5_DIGEST_SIZE / sizeof(uint32_t)];
    struct md5_ctx s[2];
    s[0] = s[1] = random_md5_state;

    if (hard_LC_COLLATE) {
        char const *lima = texta + lena;
        char const *limb = textb + lenb;

        while (true) {
            size_t guess_bufsize = 3 * (lena + lenb) + 2;
            if (bufsize < guess_bufsize) {
                bufsize = MAX(guess_bufsize, bufsize * 3 / 2);
                free(allocated);
                buf = malloc(bufsize);
                if (!buf) return -1;
                allocated = buf;
            }

            size_t sizea = (texta < lima ? xstrxfrm(buf, texta, bufsize) + 1 : 0);
            bool a_fits = sizea <= bufsize;
            size_t sizeb = (textb < limb ? (xstrxfrm((a_fits ? buf + sizea : NULL), textb, (a_fits ? bufsize - sizea : 0)) + 1) : 0);

            if (!(a_fits && sizea + sizeb <= bufsize)) {
                bufsize = sizea + sizeb;
                if (bufsize < SIZE_MAX / 3)
                    bufsize = bufsize * 3 / 2;
                free(allocated);
                buf = malloc(bufsize);
                if (!buf) return -1;
                allocated = buf;
                if (texta < lima)
                    strxfrm(buf, texta, sizea);
                if (textb < limb)
                    strxfrm(buf + sizea, textb, sizeb);
            }

            if (texta < lima)
                texta += strlen(texta) + 1;
            if (textb < limb)
                textb += strlen(textb) + 1;
            if (!(texta < lima || textb < limb)) {
                lena = sizea;
                texta = buf;
                lenb = sizeb;
                textb = buf + sizea;
                break;
            }

            md5_process_bytes(buf, sizea, &s[0]);
            md5_process_bytes(buf + sizea, sizeb, &s[1]);

            if (!xfrm_diff) {
                xfrm_diff = memcmp(buf, buf + sizea, MIN(sizea, sizeb));
                if (!xfrm_diff)
                    xfrm_diff = _GL_CMP(sizea, sizeb);
            }
        }
    }

    md5_process_bytes(texta, lena, &s[0]);
    md5_finish_ctx(&s[0], dig[0]);
    md5_process_bytes(textb, lenb, &s[1]);
    md5_finish_ctx(&s[1], dig[1]);
    int diff = memcmp(dig[0], dig[1], sizeof(dig[0]));

    if (!diff) {
        if (!xfrm_diff) {
            xfrm_diff = memcmp(texta, textb, MIN(lena, lenb));
            if (!xfrm_diff)
                xfrm_diff = _GL_CMP(lena, lenb);
        }
        diff = xfrm_diff;
    }

    free(allocated);
    return diff;
}

/* Return the printable width of the block of memory starting at
   TEXT and ending just before LIM, counting each tab as one byte.
   FIXME: Should we generally be counting non printable chars?  */

#include <stddef.h>
#include <stdbool.h>

static size_t debug_width(char const *text, char const *lim) {
    size_t width = mbsnwidth(text, lim - text, 0);
    while (text < lim) {
        if (*text == '\t') {
            ++width;
        }
        ++text;
    }
    return width;
}

/* For debug mode, "underline" a key at the
   specified offset and screen width.  */

#include <stdio.h>

static void mark_key(size_t offset, size_t width) {
  for (size_t i = 0; i < offset; i++) {
    putchar(' ');
  }

  if (width == 0) {
    puts(_("^ no match for key"));
  } else {
    for (size_t i = 0; i < width; i++) {
      putchar('_');
    }
    putchar('\n');
  }
}

/* Return true if KEY is a numeric key.  */

static inline bool key_numeric(const struct keyfield *key) {
    return key->numeric || key->general_numeric || key->human_numeric;
}

/* For LINE, output a debugging line that underlines KEY in LINE.
   If KEY is null, underline the whole line.  */

#include <stddef.h>
#include <string.h>
#include <limits.h>
#include <ctype.h>

#define SIZE_MAX ((size_t)-1)
#define MAX(a, b) ((a) > (b) ? (a) : (b))

struct line {
    char *text;
    size_t length;
};

struct keyfield {
    size_t sword;
    size_t eword;
    int skipsblanks;
    int month;
    int general_numeric;
    int numeric;
    int human_numeric;
};

static char *begfield(struct line const *line, struct keyfield const *key);
static char *limfield(struct line const *line, struct keyfield const *key);
static int key_numeric(struct keyfield const *key);
static void getmonth(char *text, char **lim);
static void ignore_value(long double value);
static char traverse_raw_number(char const **p);
static void mark_key(size_t offset, size_t width);
static size_t debug_width(char const *start, char const *end);
static int blanks(unsigned char c);
extern int unit_order[];

static void debug_key(struct line const *line, struct keyfield const *key) {
    char *text = line->text;
    char *beg = text;
    char *lim = text + line->length - 1;
    char saved;
    char *tighter_lim;

    if (key) {
        if (key->sword != SIZE_MAX)
            beg = begfield(line, key);
        if (key->eword != SIZE_MAX) {
            lim = limfield(line, key);
            lim = MAX(beg, lim);
        }

        if ((key->skipsblanks && key->sword == SIZE_MAX) || key->month || key_numeric(key)) {
            saved = *lim;
            *lim = '\0';

            while (blanks((unsigned char)*beg))
                beg++;

            tighter_lim = beg;

            if (lim < beg)
                tighter_lim = lim;
            else if (key->month)
                getmonth(beg, &tighter_lim);
            else if (key->general_numeric)
                ignore_value(strtold(beg, &tighter_lim));
            else if (key->numeric || key->human_numeric) {
                char const *p = beg + (beg < lim && *beg == '-');
                char max_digit = traverse_raw_number(&p);
                if ('0' <= max_digit) {
                    unsigned char ch = *p;
                    tighter_lim = (char *)p + (key->human_numeric && unit_order[ch]);
                }
            } else
                tighter_lim = lim;

            *lim = saved;
            lim = tighter_lim;
        }
    }

    size_t offset = debug_width(text, beg);
    size_t width = debug_width(beg, lim);
    mark_key(offset, width);
}

/* Debug LINE by underlining its keys.  */

static void debug_line(struct line const *line) {
    for (struct keyfield const *key = keylist; key != NULL; key = key->next) {
        debug_key(line, key);
        if (unique || stable) break;
    }
}

/* Return whether sorting options specified for key.  */

static bool default_key_compare(struct keyfield const *key) {
    if (key->ignore || key->translate || key->skipsblanks || key->skipeblanks ||
        key_numeric(key) || key->month || key->version || key->random) {
        return false;
    }
    return true;
}

/* Convert a key to the short options used to specify it.  */

static void key_to_opts(struct keyfield const *key, char *opts) {
    if (!key || !opts) {
        return;
    }
    if (key->skipsblanks || key->skipeblanks) {
        *opts++ = 'b';
    }
    switch (key->ignore) {
        case nondictionary:
            *opts++ = 'd';
            break;
        case nonprinting:
            *opts++ = 'i';
            break;
    }
    if (key->translate) *opts++ = 'f';
    if (key->general_numeric) *opts++ = 'g';
    if (key->human_numeric) *opts++ = 'h';
    if (key->month) *opts++ = 'M';
    if (key->numeric) *opts++ = 'n';
    if (key->random) *opts++ = 'R';
    if (key->reverse) *opts++ = 'r';
    if (key->version) *opts++ = 'V';
    *opts = '\0';
}

/* Output data independent key warnings to stderr.  */

#include <stdbool.h>
#include <limits.h>
#include <string.h>
#include <stdio.h>
#include <locale.h>
#include <error.h>

static void key_warnings(struct keyfield const *gkey, bool gkey_only) {
    struct keyfield const *key;
    struct keyfield ugkey = *gkey;
    unsigned long keynum = 1;
    bool basic_numeric_field = false;
    bool general_numeric_field = false;
    bool basic_numeric_field_span = false;
    bool general_numeric_field_span = false;
    bool number_locale_warned = false;

    for (key = keylist; key; key = key->next, keynum++) {
        if (key_numeric(key)) {
            basic_numeric_field |= !key->general_numeric;
            general_numeric_field |= key->general_numeric;
        }

        if (key->traditional_used) {
            size_t sword = key->sword == SIZE_MAX ? SIZE_MAX : key->sword;
            size_t eword = key->eword;
            char tmp[INT_BUFSIZE_BOUND(uintmax_t)];
            char obuf[INT_BUFSIZE_BOUND(sword) * 2 + 4];
            char nbuf[INT_BUFSIZE_BOUND(sword) * 2 + 5];
            snprintf(obuf, sizeof obuf, "+%s -%s", umaxtostr(sword, tmp), umaxtostr(eword + 1, tmp));
            snprintf(nbuf, sizeof nbuf, "-k %s,%s", umaxtostr(sword + 1, tmp), 
                     umaxtostr(eword + 1 + (key->echar == SIZE_MAX), tmp));
            error(0, 0, _("obsolescent key %s used; consider %s instead"), quote_n(0, obuf), quote_n(1, nbuf));
        }

        bool zero_width = key->sword != SIZE_MAX && key->eword < key->sword;
        if (zero_width)
            error(0, 0, _("key %lu has zero width and will be ignored"), keynum);

        bool implicit_skip = key_numeric(key) || key->month;
        bool line_offset = key->eword == 0 && key->echar != 0;
        if (!zero_width && !gkey_only && tab == TAB_DEFAULT && !line_offset &&
            ((!key->skipsblanks && !implicit_skip) || (!key->skipsblanks && key->schar) || 
             (!key->skipeblanks && key->echar)))
            error(0, 0, _("leading blanks are significant in key %lu; consider also specifying 'b'"), keynum);

        if (!gkey_only && key_numeric(key) && (key->sword + 1 < key->eword + 1 || !key->sword + 1)) {
            error(0, 0, _("key %lu is numeric and spans multiple fields"), keynum);
            general_numeric_field_span |= key->general_numeric;
            basic_numeric_field_span |= !key->general_numeric;
        }

        if (ugkey.ignore == key->ignore) ugkey.ignore = NULL;
        if (ugkey.translate == key->translate) ugkey.translate = NULL;
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

    if (basic_numeric_field_span &&
        (tab == TAB_DEFAULT ? (thousands_sep != NON_CHAR && isblank(to_uchar(thousands_sep))) 
        : tab == thousands_sep)) {
        error(0, 0, _("field separator %s is treated as a group separator in numbers"),
              quote(((char[]){thousands_sep, 0})));
        number_locale_warned = true;
    }

    if (basic_numeric_field_span || general_numeric_field_span) {
        if (tab == TAB_DEFAULT ? (decimal_point != NON_CHAR && isblank(to_uchar(decimal_point)))
            : tab == decimal_point) {
            error(0, 0, _("field separator %s is treated as a decimal point in numbers"),
                  quote(((char[]){decimal_point, 0})));
            number_locale_warned = true;
        } else if (tab == '-') {
            error(0, 0, _("field separator %s is treated as a minus sign in numbers"),
                  quote(((char[]){tab, 0})));
        } else if (general_numeric_field_span && tab == '+') {
            error(0, 0, _("field separator %s is treated as a plus sign in numbers"),
                  quote(((char[]){tab, 0})));
        }
    }

    if ((basic_numeric_field || general_numeric_field) && !number_locale_warned) {
        error(0, 0, _("numbers use %s as a decimal point in this locale"),
              quote(((char[]){decimal_point, 0})));
    }

    if (basic_numeric_field && thousands_sep_ignored) {
        error(0, 0, _("the multi-byte number group separator in this locale is not supported"));
    }

    if (!default_key_compare(&ugkey) || (ugkey.reverse && (stable || unique) && keylist)) {
        bool ugkey_reverse = ugkey.reverse;
        if (!(stable || unique))
            ugkey.reverse = false;

        char opts[sizeof short_options];
        key_to_opts(&ugkey, opts);
        error(0, 0, ngettext("option '-%s' is ignored", "options '-%s' are ignored", select_plural(strlen(opts))), opts);

        ugkey.reverse = ugkey_reverse;
    }

    if (ugkey.reverse && !(stable || unique) && keylist) {
        error(0, 0, _("option '-r' only applies to last-resort comparison"));
    }
}

/* Return either the sense of DIFF or its reverse, depending on REVERSED.
   If REVERSED, do not simply negate DIFF as that can mishandle INT_MIN.  */

#include <stdbool.h>

static int diff_reversed(int diff, bool reversed) {
    return reversed ? (diff > 0 ? -1 : (diff < 0 ? 1 : 0)) : diff;
}

/* Compare two lines A and B trying every key in sequence until there
   are no more keys or a difference is found. */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define NONZERO(a) ((a) != 0)
#define _GL_CMP(a, b) (((a) > (b)) - ((a) < (b)))
#define to_uchar(c) ((unsigned char) (c))
#define SIZE_MAX ((size_t) -1)

struct line {
    char *keybeg;
    char *keylim;
    char *text;
    size_t length;
};

struct keyfield {
    const char *translate;
    const bool *ignore;
    bool numeric;
    bool general_numeric;
    bool human_numeric;
    bool month;
    bool random;
    bool version;
    size_t eword;
    size_t sword;
    bool skipsblanks;
    struct keyfield *next;
};

char *begfield(struct line const *a, struct keyfield const *key);
char *limfield(struct line const *a, struct keyfield const *key);
int numcompare(const char *a, const char *b);
int general_numcompare(const char *a, const char *b);
int human_numcompare(const char *a, const char *b);
int getmonth(const char *a, const char *b);
int compare_random(const char *a, size_t alen, const char *b, size_t blen);
int filenvercmp(const char *a, size_t alen, const char *b, size_t blen);
int xmemcoll0(const char *a, size_t alen, const char *b, size_t blen);
int diff_reversed(int diff, bool reverse);

static int keycompare(struct line const *a, struct line const *b) {
    struct keyfield *key = keylist;
    char *texta = a->keybeg;
    char *textb = b->keybeg;
    char *lima = a->keylim;
    char *limb = b->keylim;
    int diff;

    while (true) {
        char const *translate = key->translate;
        bool const *ignore = key->ignore;

        lima = MAX(texta, lima);
        limb = MAX(textb, limb);

        size_t lena = lima - texta;
        size_t lenb = limb - textb;

        if (hard_LC_COLLATE || key_numeric(key) || key->month || key->random || key->version) {
            char *ta = texta;
            char *tb = textb;
            size_t tlena = lena;
            size_t tlenb = lenb;

            char *allocated = NULL;
            char stackbuf[4000];

            if (ignore || translate) {
                size_t size = lena + 1 + lenb + 1;
                ta = size <= sizeof stackbuf ? stackbuf : allocated = xmalloc(size);
                tb = ta + lena + 1;

                for (size_t i = 0, j = 0; i < lena; i++)
                    if (!(ignore && ignore[to_uchar(texta[i])]))
                        ta[j++] = translate ? translate[to_uchar(texta[i])] : texta[i];
                tlena = strlen(ta);

                for (size_t i = 0, j = 0; i < lenb; i++)
                    if (!(ignore && ignore[to_uchar(textb[i])]))
                        tb[j++] = translate ? translate[to_uchar(textb[i])] : textb[i];
                tlenb = strlen(tb);
            }

            ta[tlena] = '\0';
            tb[tlenb] = '\0';

            if (key->numeric)
                diff = numcompare(ta, tb);
            else if (key->general_numeric)
                diff = general_numcompare(ta, tb);
            else if (key->human_numeric)
                diff = human_numcompare(ta, tb);
            else if (key->month)
                diff = getmonth(ta, NULL) - getmonth(tb, NULL);
            else if (key->random)
                diff = compare_random(ta, tlena, tb, tlenb);
            else if (key->version)
                diff = filenvercmp(ta, tlena, tb, tlenb);
            else
                diff = xmemcoll0(ta, tlena + 1, tb, tlenb + 1);

            free(allocated);
        } else if (ignore) {
            while (true) {
                while (texta < lima && ignore[to_uchar(*texta)]) ++texta;
                while (textb < limb && ignore[to_uchar(*textb)]) ++textb;

                if (!(texta < lima && textb < limb)) {
                    diff = (texta < lima) - (textb < limb);
                    break;
                }

                diff = to_uchar(translate ? translate[to_uchar(*texta)] : *texta) -
                       to_uchar(translate ? translate[to_uchar(*textb)] : *textb);

                if (diff) break;
                ++texta;
                ++textb;
            }
        } else {
            size_t lenmin = MIN(lena, lenb);
            if (lenmin == 0) {
                diff = _GL_CMP(lena, lenb);
            } else if (translate) {
                for (size_t i = 0; i < lenmin; ++i) {
                    diff = to_uchar(translate[to_uchar(texta[i])]) -
                           to_uchar(translate[to_uchar(textb[i])]);
                    if (diff) break;
                }
            } else {
                diff = memcmp(texta, textb, lenmin);
            }

            if (!diff) diff = _GL_CMP(lena, lenb);
        }

        if (diff) break;

        key = key->next;
        if (!key) return 0;

        if (key->eword != SIZE_MAX)
            lima = limfield(a, key);
        else
            lima = a->text + a->length;

        if (key->eword != SIZE_MAX)
            limb = limfield(b, key);
        else
            limb = b->text + b->length;

        if (key->sword != SIZE_MAX)
            texta = begfield(a, key);
        else {
            texta = a->text;
            if (key->skipsblanks)
                while (texta < lima && blanks[to_uchar(*texta)]) ++texta;
        }

        if (key->sword != SIZE_MAX)
            textb = begfield(b, key);
        else {
            textb = b->text;
            if (key->skipsblanks)
                while (textb < limb && blanks[to_uchar(*textb)]) ++textb;
        }
    }

    return diff_reversed(diff, key->reverse);
}

/* Compare two lines A and B, returning negative, zero, or positive
   depending on whether A compares less than, equal to, or greater than B. */

static int compare(struct line const *a, struct line const *b) {
    size_t alen = a->length - 1;
    size_t blen = b->length - 1;

    if (keylist) {
        int diff = keycompare(a, b);
        if (diff || unique || stable) {
            return diff;
        }
    }

    if (alen == 0 || blen == 0) {
        return alen - blen;
    }

    int diff = hard_LC_COLLATE ? xmemcoll0(a->text, alen + 1, b->text, blen + 1)
                               : memcmp(a->text, b->text, MIN(alen, blen));

    return diff != 0 ? diff : diff_reversed(alen - blen, reverse);
}

/* Write LINE to output stream FP; the output file's name is
   OUTPUT_FILE if OUTPUT_FILE is non-null, and is the standard output
   otherwise.  If debugging is enabled and FP is standard output,
   append some debugging information.  */

#include <stdio.h>
#include <stdlib.h>

static void write_line(struct line const *line, FILE *fp, char const *output_file) {
    char *buf = line->text;
    size_t n_bytes = line->length;

    if (!output_file && debug) {
        for (size_t i = 0; i < n_bytes; i++) {
            char wc = buf[i];
            if (wc == '\t')
                wc = '>';
            else if (i == n_bytes - 1)
                wc = '\n';
            if (fputc(wc, fp) == EOF) {
                perror("write failed");
                exit(EXIT_FAILURE);
            }
        }
        debug_line(line);
    } else {
        buf[n_bytes - 1] = eolchar;
        if (fwrite(buf, 1, n_bytes, fp) != n_bytes) {
            perror("write failed");
            exit(EXIT_FAILURE);
        }
        buf[n_bytes - 1] = '\0';
    }
}

/* Check that the lines read from FILE_NAME come in order.  Return
   true if they are in order.  If CHECKONLY == 'c', also print a
   diagnostic (FILE_NAME, line number, contents of line) to stderr if
   they are not in order.  */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static bool check(const char *file_name, char checkonly) {
    FILE *fp = xfopen(file_name, "r");
    struct buffer buf;
    struct line temp = {nullptr, 0, nullptr, nullptr};
    size_t alloc = 0;
    uintmax_t line_number = 0;
    struct keyfield const *key = keylist;
    bool ordered = true;

    initbuf(&buf, sizeof(struct line), MAX(merge_buffer_size, sort_size));

    while (fillbuf(&buf, fp, file_name)) {
        struct line const *line = buffer_linelim(&buf);
        struct line const *linebase = line - buf.nlines;

        if (alloc && !unique <= compare(&temp, line - 1)) {
            if (checkonly == 'c') {
                struct line const *disorder_line = line - 1;
                uintmax_t disorder_line_number = buffer_linelim(&buf) - disorder_line + line_number;
                char hr_buf[INT_BUFSIZE_BOUND(disorder_line_number)];
                fprintf(stderr, _("%s: %s:%s: disorder: "), program_name, file_name, umaxtostr(disorder_line_number, hr_buf));
                write_line(disorder_line, stderr, _("standard error"));
            }
            ordered = false;
            break;
        }

        while (linebase < --line) {
            if (!unique <= compare(line, line - 1)) {
                if (checkonly == 'c') {
                    struct line const *disorder_line = line;
                    uintmax_t disorder_line_number = buffer_linelim(&buf) - disorder_line + line_number;
                    char hr_buf[INT_BUFSIZE_BOUND(disorder_line_number)];
                    fprintf(stderr, _("%s: %s:%s: disorder: "), program_name, file_name, umaxtostr(disorder_line_number, hr_buf));
                    write_line(disorder_line, stderr, _("standard error"));
                }
                ordered = false;
                break;
            }
        }

        if (!ordered) break;

        line_number += buf.nlines;

        if (alloc < line->length) {
            alloc = line->length;
            temp.text = xrealloc(temp.text, alloc);
        }
        memcpy(temp.text, line->text, line->length);
        temp.length = line->length;
        if (key) {
            temp.keybeg = temp.text + (line->keybeg - line->text);
            temp.keylim = temp.text + (line->keylim - line->text);
        }
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

#include <stdlib.h>
#include <stdio.h>

static size_t open_input_files(struct sortfile *files, size_t nfiles, FILE ***pfps) {
    size_t opened_files_count = 0;
    FILE **fps = xnmalloc(nfiles, sizeof(*fps));
    if (!fps) {
        /* Handle memory allocation failure */
        return 0;
    }
    *pfps = fps;

    for (size_t i = 0; i < nfiles; i++) {
        struct sortfile file = files[i];
        if (file.temp && file.temp->state != UNCOMPRESSED) {
            fps[i] = open_temp(file.temp);
        } else {
            fps[i] = stream_open(file.name, "r");
        }

        if (!fps[i]) {
            break;
        }
        opened_files_count++;
    }

    return opened_files_count;
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   FPS is the vector of open stream corresponding to the files.
   Close input and output streams before returning.
   OUTPUT_FILE gives the name of the output file.  If it is null,
   the output file is standard output.  */

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static void mergefps(struct sortfile* files, size_t ntemps, size_t nfiles,
    FILE* ofp, const char* output_file, FILE** fps) {

    struct buffer* buffers = calloc(nfiles, sizeof(struct buffer));
    struct line saved;
    const struct line* savedline = NULL;
    size_t savealloc = 0;
    const struct line** cur = calloc(nfiles, sizeof(struct line*));
    const struct line** base = calloc(nfiles, sizeof(struct line*));
    size_t* ord = calloc(nfiles, sizeof(size_t));
    saved.text = NULL;

    for (size_t i = 0; i < nfiles;) {
        initbuf(&buffers[i], sizeof(struct line), 
            MAX(merge_buffer_size, sort_size / nfiles));

        if (fillbuf(&buffers[i], fps[i], files[i].name)) {
            const struct line* linelim = buffer_linelim(&buffers[i]);
            cur[i] = linelim - 1;
            base[i] = linelim - buffers[i].nlines;
            ord[i] = i;
            i++;
        } else {
            xfclose(fps[i], files[i].name);
            if (i < ntemps) {
                ntemps--;
                zaptemp(files[i].name);
            }
            free(buffers[i].buf);
            --nfiles;
            for (size_t j = i; j < nfiles; ++j) {
                files[j] = files[j + 1];
                fps[j] = fps[j + 1];
            }
        }
    }

    for (size_t i = 1; i < nfiles; i++) {
        for (size_t j = i; j > 0 && compare(cur[ord[j - 1]], cur[ord[j]]) > 0; j--) {
            size_t temp = ord[j];
            ord[j] = ord[j - 1];
            ord[j - 1] = temp;
        }
    }

    while (nfiles) {
        const struct line* smallest = cur[ord[0]];
        if (unique && (!savedline || compare(savedline, smallest))) {
            if (savedline) write_line(&saved, ofp, output_file);
            savedline = &saved;
            if (savealloc < smallest->length) {
                savealloc = smallest->length * 2;
                free(saved.text);
                saved.text = malloc(savealloc);
            }
            saved.length = smallest->length;
            memcpy(saved.text, smallest->text, saved.length);
            if (keylist) {
                saved.keybeg = saved.text + (smallest->keybeg - smallest->text);
                saved.keylim = saved.text + (smallest->keylim - smallest->text);
            }
        } else if (!unique) {
            write_line(smallest, ofp, output_file);
        }

        if (base[ord[0]] < smallest) {
            cur[ord[0]] = smallest - 1;
        } else if (fillbuf(&buffers[ord[0]], fps[ord[0]], files[ord[0]].name)) {
            const struct line* linelim = buffer_linelim(&buffers[ord[0]]);
            cur[ord[0]] = linelim - 1;
            base[ord[0]] = linelim - buffers[ord[0]].nlines;
        } else {
            xfclose(fps[ord[0]], files[ord[0]].name);
            if (ord[0] < ntemps) {
                ntemps--;
                zaptemp(files[ord[0]].name);
            }
            free(buffers[ord[0]].buf);
            --nfiles;
            for (size_t i = ord[0]; i < nfiles; ++i) {
                files[i] = files[i + 1];
                fps[i] = fps[i + 1];
                buffers[i] = buffers[i + 1];
                cur[i] = cur[i + 1];
                base[i] = base[i + 1];
            }
            for (size_t i = 0; i < nfiles; ++i) {
                ord[i] = ord[i + 1];
            }
            continue;
        }

        // Reorder ord array
        size_t lo = 1, hi = nfiles, ord0 = ord[0];
        while (lo < hi) {
            size_t probe = (lo + hi) / 2;
            int cmp = compare(cur[ord0], cur[ord[probe]]);
            if (cmp < 0 || (cmp == 0 && ord0 < ord[probe])) {
                hi = probe;
            } else {
                lo = probe + 1;
            }
        }

        size_t pos = lo - 1;
        memmove(ord, ord + 1, pos * sizeof(size_t));
        ord[pos] = ord0;
    }

    if (unique && savedline) {
        write_line(&saved, ofp, output_file);
        free(saved.text);
    }

    xfclose(ofp, output_file);
    free(fps);
    free(buffers);
    free(ord);
    free(base);
    free(cur);
}

/* Merge lines from FILES onto OFP.  NTEMPS is the number of temporary
   files (all of which are at the start of the FILES array), and
   NFILES is the number of files; 0 <= NTEMPS <= NFILES <= NMERGE.
   Close input and output files before returning.
   OUTPUT_FILE gives the name of the output file.

   Return the number of files successfully merged.  This number can be
   less than NFILES if we ran low on file descriptors, but in this
   case it is never less than 2.  */

#include <stdio.h>
#include <stddef.h>

static size_t mergefiles(struct sortfile *files, size_t ntemps, size_t nfiles, FILE *ofp, const char *output_file) {
    FILE **fps;
    size_t nopened = open_input_files(files, nfiles, &fps);
    if (nopened < 2) {
        sort_die("open failed", files[nopened].name);
    }
    mergefps(files, ntemps, nopened, ofp, output_file, fps);
    return nopened;
}

/* Merge into T (of size NLINES) the two sorted arrays of lines
   LO (with NLINES / 2 members), and
   T - (NLINES / 2) (with NLINES - NLINES / 2 members).
   T and LO point just past their respective arrays, and the arrays
   are in reverse order.  NLINES must be at least 2.  */

static void mergelines(struct line *restrict t, size_t nlines, struct line const *restrict lo) {
    size_t nlo = nlines / 2;
    size_t nhi = nlines - nlo;
    struct line *hi = t - nlo;

    while (nlo > 0 && nhi > 0) {
        if (compare(lo - 1, hi - 1) <= 0) {
            *--t = *--lo;
            nlo--;
        } else {
            *--t = *--hi;
            nhi--;
        }
    }

    while (nlo > 0) {
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

static void sequential_sort(struct line *restrict lines, size_t nlines, struct line *restrict temp, bool to_temp) {
    if (nlines == 2) {
        int swap = (compare(&lines[-1], &lines[-2]) > 0);
        if (to_temp) {
            temp[-1] = lines[-1 - swap];
            temp[-2] = lines[-2 + swap];
        } else {
            if (swap) {
                struct line temp_swap = lines[-1];
                lines[-1] = lines[-2];
                lines[-2] = temp_swap;
            }
        }
        return;
    }
    
    size_t nlo = nlines / 2;
    size_t nhi = nlines - nlo;
    struct line *dest = to_temp ? temp : lines;
    struct line *sorted_lo = to_temp ? lines : temp;
    size_t offset = to_temp ? nlo : 0;

    sequential_sort(lines - nlo, nhi, temp - offset, to_temp);
    if (nlo > 1) {
        sequential_sort(lines, nlo, temp, !to_temp);
    } else if (!to_temp) {
        temp[-1] = lines[-1];
    }
    
    mergelines(dest, nlines, sorted_lo);
}

static struct merge_node *init_node (struct merge_node *restrict,
                                     struct merge_node *restrict,
                                     struct line *, size_t, size_t, bool);


/* Create and return a merge tree for NTHREADS threads, sorting NLINES
   lines, with destination DEST.  */
struct merge_node *merge_tree_init(size_t nthreads, size_t nlines, struct line *dest) {
    struct merge_node *merge_tree = xmalloc(2 * sizeof(*merge_tree) * nthreads);
    if (!merge_tree) {
        return NULL; // handle memory allocation failure
    }

    struct merge_node *root = merge_tree;
    root->lo = root->hi = root->end_lo = root->end_hi = NULL;
    root->dest = NULL;
    root->nlo = root->nhi = nlines;
    root->parent = NULL;
    root->level = MERGE_END;
    root->queued = false;

    if (pthread_mutex_init(&root->lock, NULL) != 0) {
        free(merge_tree); // ensure cleanup on error
        return NULL;
    }

    if (!init_node(root, root + 1, dest, nthreads, nlines, false)) {
        pthread_mutex_destroy(&root->lock);
        free(merge_tree); // ensure cleanup on error
        return NULL;
    }

    return merge_tree;
}

/* Destroy the merge tree. */
#include <pthread.h>
#include <stdlib.h>

static void merge_tree_destroy(size_t nthreads, struct merge_node *merge_tree) {
    if (!merge_tree) return;

    size_t n_nodes = nthreads * 2;
    for (size_t i = 0; i < n_nodes; i++) {
        pthread_mutex_destroy(&merge_tree[i].lock);
    }

    free(merge_tree);
}

/* Initialize a merge tree node and its descendants.  The node's
   parent is PARENT.  The node and its descendants are taken from the
   array of nodes NODE_POOL.  Their destination starts at DEST; they
   will consume NTHREADS threads.  The total number of sort lines is
   TOTAL_LINES.  IS_LO_CHILD is true if the node is the low child of
   its parent.  */

static struct merge_node *init_node(struct merge_node *restrict parent, struct merge_node *restrict node_pool, struct line *dest, size_t nthreads, size_t total_lines, bool is_lo_child) {
    size_t nlines = is_lo_child ? parent->nlo : parent->nhi;
    size_t nlo = nlines / 2;
    size_t nhi = nlines - nlo;
    struct line *lo = dest - total_lines;
    struct line *hi = lo - nlo;
    struct line **parent_end = is_lo_child ? &parent->end_lo : &parent->end_hi;

    struct merge_node *node = node_pool++;
    node->lo = node->end_lo = lo;
    node->hi = node->end_hi = hi;
    node->dest = parent_end;
    node->nlo = nlo;
    node->nhi = nhi;
    node->parent = parent;
    node->level = parent->level + 1;
    node->queued = false;
    if (pthread_mutex_init(&node->lock, NULL) != 0) {
        return NULL; // Handle mutex initialization failure
    }

    node->lo_child = NULL;
    node->hi_child = NULL;

    if (nthreads > 1) {
        size_t lo_threads = nthreads / 2;
        size_t hi_threads = nthreads - lo_threads;
        node->lo_child = node_pool;
        node_pool = init_node(node, node_pool, lo, lo_threads, total_lines, true);
        if (!node_pool) return NULL; // Handle recursive allocation failure

        node->hi_child = node_pool;
        node_pool = init_node(node, node_pool, hi, hi_threads, total_lines, false);
        if (!node_pool) return NULL; // Handle recursive allocation failure
    }
    
    return node_pool;
}


/* Compare two merge nodes A and B for priority.  */

#include <stdlib.h>

static int compare_nodes(const void *a, const void *b) {
    const struct merge_node *nodea = a;
    const struct merge_node *nodeb = b;
    
    int level_diff = nodea->level - nodeb->level;
    if (level_diff != 0) {
        return level_diff;
    }

    int sum_nodea = nodea->nlo + nodea->nhi;
    int sum_nodeb = nodeb->nlo + nodeb->nhi;

    return sum_nodea - sum_nodeb;
}

/* Lock a merge tree NODE.  */

#include <pthread.h>
#include <errno.h>

static inline int lock_node(struct merge_node *node) {
    if (node == NULL) {
        return EINVAL; // Invalid argument
    }
    int res = pthread_mutex_lock(&node->lock);
    return res;
}

/* Unlock a merge tree NODE. */

#include <pthread.h>

void unlock_node(struct merge_node *node) {
    if (node == NULL) {
        return;
    }
    pthread_mutex_unlock(&node->lock);
}

/* Destroy merge QUEUE. */

static void queue_destroy(struct merge_node_queue *queue) {
    if (queue == NULL) return;
    
    if (queue->priority_queue != NULL) {
        heap_free(queue->priority_queue);
        queue->priority_queue = NULL;
    }

    int cond_result = pthread_cond_destroy(&queue->cond);
    if (cond_result != 0) {
        // Handle condition variable destruction error
        return;
    }
    
    int mutex_result = pthread_mutex_destroy(&queue->mutex);
    if (mutex_result != 0) {
        // Handle mutex destruction error
        return;
    }
}

/* Initialize merge QUEUE, allocating space suitable for a maximum of
   NTHREADS threads.  */

#include <stddef.h>
#include <pthread.h>

static void queue_init(struct merge_node_queue *queue, size_t nthreads) {
    if (queue == NULL) {
        return;
    }

    queue->priority_queue = heap_alloc(compare_nodes, 2 * nthreads);
    if (queue->priority_queue == NULL) {
        // Handle allocation failure if needed
        return;
    }

    if (pthread_mutex_init(&queue->mutex, NULL) != 0) {
        // Handle mutex initialization failure if needed
        return;
    }

    if (pthread_cond_init(&queue->cond, NULL) != 0) {
        // Handle condition variable initialization failure if needed
        pthread_mutex_destroy(&queue->mutex);
        return;
    }
}

/* Insert NODE into QUEUE.  The caller either holds a lock on NODE, or
   does not need to lock NODE.  */

static void queue_insert(struct merge_node_queue *queue, struct merge_node *node) {
  if (queue == NULL || node == NULL) {
    return; // handle invalid input gracefully
  }

  pthread_mutex_lock(&queue->mutex);
  heap_insert(queue->priority_queue, node);
  node->queued = true;
  pthread_cond_signal(&queue->cond);
  pthread_mutex_unlock(&queue->mutex);
}

/* Pop the top node off the priority QUEUE, lock the node, return it.  */

static struct merge_node *queue_pop(struct merge_node_queue *queue) {
    struct merge_node *node = NULL;
    pthread_mutex_lock(&queue->mutex);
    while ((node = heap_remove_top(queue->priority_queue)) == NULL) {
        pthread_cond_wait(&queue->cond, &queue->mutex);
    }
    if (node != NULL) {
        lock_node(node);
        node->queued = false;
    }
    pthread_mutex_unlock(&queue->mutex);
    return node;
}

/* Output LINE to TFP, unless -u is specified and the line compares
   equal to the previous line.  TEMP_OUTPUT is the name of TFP, or
   is null if TFP is standard output.

   This function does not save the line for comparison later, so it is
   appropriate only for internal sort.  */

#include <stdbool.h>
#include <stdio.h>

static void write_unique(struct line const *line, FILE *tfp, const char *temp_output) {
    static struct line saved_line = {0};
    static bool is_saved_line_initialized = false;

    if (unique && is_saved_line_initialized && !compare(line, &saved_line)) {
        return;
    }

    if (unique) {
        saved_line = *line;
        is_saved_line_initialized = true;
    }

    write_line(line, tfp, temp_output);
}

/* Merge the lines currently available to a NODE in the binary
   merge tree.  Merge a number of lines appropriate for this merge
   level, assuming TOTAL_LINES is the total number of lines.

   If merging at the top level, send output to TFP.  TEMP_OUTPUT is
   the name of TFP, or is null if TFP is standard output.  */

#include <stddef.h>
#include <stdio.h>

static void mergelines_node(struct merge_node *restrict node, size_t total_lines, FILE *tfp, char const *temp_output) {
    struct line *lo_orig = node->lo;
    struct line *hi_orig = node->hi;
    size_t to_merge = MAX_MERGE(total_lines, node->level);
    struct line *dest = (node->level > MERGE_ROOT) ? *node->dest : NULL;

    while (to_merge--) {
        if (node->lo == node->end_lo || node->hi == node->end_hi) break;

        int cmp_result = compare(node->lo - 1, node->hi - 1);
        if (cmp_result <= 0) {
            if (dest) *--dest = *--node->lo;
            else write_unique(--node->lo, tfp, temp_output);
        } else {
            if (dest) *--dest = *--node->hi;
            else write_unique(--node->hi, tfp, temp_output);
        }
    }

    size_t merged_lo = lo_orig - node->lo;
    size_t merged_hi = hi_orig - node->hi;

    if (node->nhi == merged_hi) {
        while (node->lo != node->end_lo && to_merge--)
            if (dest) *--dest = *--node->lo;
            else write_unique(--node->lo, tfp, temp_output);
    } else if (node->nlo == merged_lo) {
        while (node->hi != node->end_hi && to_merge--)
            if (dest) *--dest = *--node->hi;
            else write_unique(--node->hi, tfp, temp_output);
    }
    
    if (dest) *node->dest = dest;
    node->nlo -= merged_lo;
    node->nhi -= merged_hi;
}

/* Into QUEUE, insert NODE if it is not already queued, and if one of
   NODE's children has available lines and the other either has
   available lines or has exhausted its lines.  */

static void
queue_check_insert(struct merge_node_queue *queue, struct merge_node *node)
{
    if (node->queued) {
        return;
    }

    bool lo_avail = (node->lo != node->end_lo);
    bool hi_avail = (node->hi != node->end_hi);

    if ((lo_avail && (hi_avail || !node->nhi)) || 
        (hi_avail && !node->nlo)) {
        queue_insert(queue, node);
    }
}

/* Into QUEUE, insert NODE's parent if the parent can now be worked on.  */

static void queue_check_insert_parent(struct merge_node_queue *queue,
                                      struct merge_node *node) {
    if (node->level > MERGE_ROOT) {
        lock_node(node->parent);
        queue_check_insert(queue, node->parent);
        unlock_node(node->parent);
        return;
    }

    if (node->nlo + node->nhi == 0) {
        queue_insert(queue, node->parent);
    }
}

/* Repeatedly pop QUEUE for a node with lines to merge, and merge at least
   some of those lines, until the MERGE_END node is popped.
   TOTAL_LINES is the total number of lines.  If merging at the top
   level, send output to TFP.  TEMP_OUTPUT is the name of TFP, or is
   null if TFP is standard output.  */

static void merge_loop(struct merge_node_queue *queue, size_t total_lines, FILE *tfp, const char *temp_output) {
    while (true) {
        struct merge_node *node = queue_pop(queue);
        
        if (!node) {
            fprintf(stderr, "Failed to pop node from queue\n");
            return; 
        }

        if (node->level == MERGE_END) {
            unlock_node(node);
            if (!queue_insert(queue, node)) {
                fprintf(stderr, "Failed to insert node back to queue\n");
                return; 
            }
            break;
        }

        if (!mergelines_node(node, total_lines, tfp, temp_output)) {
            fprintf(stderr, "Failed to merge lines\n");
            unlock_node(node);
            return;
        }

        if (!queue_check_insert(queue, node) || !queue_check_insert_parent(queue, node)) {
            fprintf(stderr, "Failed to insert node/parent back to queue\n");
            unlock_node(node);
            return;
        }

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

void *sortlines_thread(void *data) {
    if (!data) {
        return NULL;
    }
    struct thread_args const *args = data;
    sortlines(args->lines, args->nthreads, args->total_lines, args->node, args->queue, args->tfp, args->output_temp);
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

#include <pthread.h>

static void sortlines(struct line *restrict lines, size_t nthreads,
                      size_t total_lines, struct merge_node *node,
                      struct merge_node_queue *queue, FILE *tfp, const char *temp_output) {
    if (nthreads <= 1 || SUBTHREAD_LINES_HEURISTIC > (node->nlo + node->nhi)) {
        size_t nlo = node->nlo;
        size_t nhi = node->nhi;
        struct line *temp = lines - total_lines;
        if (nhi > 1) {
            sequential_sort(lines - nlo, nhi, temp - nlo / 2, false);
        }
        if (nlo > 1) {
            sequential_sort(lines, nlo, temp, false);
        }
        node->lo = lines;
        node->hi = lines - nlo;
        node->end_lo = lines - nlo;
        node->end_hi = lines - nlo - nhi;
        queue_insert(queue, node);
        merge_loop(queue, total_lines, tfp, temp_output);
        return;
    }

    size_t lo_threads = nthreads / 2;
    size_t hi_threads = nthreads - lo_threads;
    pthread_t thread;
    struct thread_args args = {
            lines, lo_threads, total_lines,
            node->lo_child, queue, tfp, temp_output
    };

    if (pthread_create(&thread, NULL, sortlines_thread, &args) == 0) {
        sortlines(lines - node->nlo, hi_threads, total_lines, node->hi_child, queue, tfp, temp_output);
        pthread_join(thread, NULL);
    } else {
        sortlines(lines, 1, total_lines, node, queue, tfp, temp_output);
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

#include <stdbool.h>
#include <stddef.h>
#include <sys/stat.h>
#include <unistd.h>

static void avoid_trashing_input(struct sortfile *files, size_t ntemps, size_t nfiles, const char *outfile) {
    struct tempnode *tempcopy = NULL;

    for (size_t i = ntemps; i < nfiles; i++) {
        bool is_stdin = STREQ(files[i].name, "-");
        bool same = false;
        struct stat instat;

        if (outfile && STREQ(outfile, files[i].name) && !is_stdin) {
            same = true;
        } else {
            struct stat *outst = get_outstatus();
            if (!outst) {
                return; // Assuming function should terminate if get_outstatus fails
            }

            if ((is_stdin ? fstat(STDIN_FILENO, &instat) : stat(files[i].name, &instat)) == 0) {
                same = psame_inode(&instat, outst);
            }
        }

        if (same) {
            if (!tempcopy) {
                FILE *tftp;
                tempcopy = create_temp(&tftp);
                mergefiles(&files[i], 0, 1, tftp, tempcopy->name);
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

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <string.h>

static void check_inputs(char *const *files, size_t nfiles) {
    for (size_t i = 0; i < nfiles; i++) {
        if (strcmp(files[i], "-") == 0) {
            continue;
        }
        
        if (access(files[i], R_OK) != 0) {
            fprintf(stderr, "Error: cannot read %s: %s\n", files[i], strerror(errno));
        }
    }
}

/* Ensure a specified output file can be created or written to,
   and point stdout to it.  Do not truncate the file.
   Exit with a diagnostic on failure.  */

#include <errno.h>

static void check_output(const char *outfile) {
    if (!outfile) return;

    int oflags = O_WRONLY | O_BINARY | O_CLOEXEC | O_CREAT;
    int outfd = open(outfile, oflags, MODE_RW_UGO);
    
    if (outfd < 0) {
        int errnum = errno;
        sort_die(strerror(errnum), outfile);
    }

    if (move_fd(outfd, STDOUT_FILENO) < 0) {
        int errnum = errno;
        close(outfd);
        sort_die(strerror(errnum), outfile);
    }
}

/* Merge the input FILES.  NTEMPS is the number of files at the
   start of FILES that are temporary; it is zero at the top level.
   NFILES is the total number of files.  Put the output in
   OUTPUT_FILE; a null OUTPUT_FILE stands for standard output.  */

static void merge(struct sortfile *files, size_t ntemps, size_t nfiles, char const *output_file) {
    while (nmerge < nfiles) {
        size_t in = 0;
        size_t out = 0;

        while (nmerge <= nfiles - in) {
            FILE *tfp;
            struct tempnode *temp = create_temp(&tfp);
            size_t num_merged = mergefiles(&files[in], MIN(ntemps, nmerge), nmerge, tfp, temp->name);
            ntemps -= MIN(ntemps, num_merged);
            files[out].name = temp->name;
            files[out].temp = temp;
            in += num_merged;
            out++;
        }

        size_t remainder = nfiles - in;
        size_t cheap_slots = nmerge - out % nmerge;

        if (cheap_slots < remainder) {
            size_t nshortmerge = remainder - cheap_slots + 1;
            FILE *tfp;
            struct tempnode *temp = create_temp(&tfp);
            size_t num_merged = mergefiles(&files[in], MIN(ntemps, nshortmerge), nshortmerge, tfp, temp->name);
            ntemps -= MIN(ntemps, num_merged);
            files[out].name = temp->name;
            files[out++].temp = temp;
            in += num_merged;
        }

        memmove(&files[out], &files[in], (nfiles - in) * sizeof(*files));
        ntemps += out;
        nfiles -= in - out;
    }

    avoid_trashing_input(files, ntemps, nfiles, output_file);

    while (1) {
        FILE **fps;
        size_t nopened = open_input_files(files, nfiles, &fps);

        if (nopened == nfiles) {
            FILE *ofp = stream_open(output_file, "w");
            if (ofp) {
                mergefps(files, ntemps, nfiles, ofp, output_file, fps);
                break;
            }
            if (errno != EMFILE || nopened <= 2) {
                sort_die(_("open failed"), output_file);
            }
        } else if (nopened <= 2) {
            sort_die(_("open failed"), files[nopened].name);
        }

        FILE *tfp;
        struct tempnode *temp;
        do {
            nopened--;
            xfclose(fps[nopened], files[nopened].name);
            temp = maybe_create_temp(&tfp, !(nopened <= 2));
        } while (!temp);

        mergefps(&files[0], MIN(ntemps, nopened), nopened, tfp, temp->name, fps);
        ntemps -= MIN(ntemps, nopened);
        files[0].name = temp->name;
        files[0].temp = temp;

        memmove(&files[1], &files[nopened], (nfiles - nopened) * sizeof(*files));
        ntemps++;
        nfiles -= nopened - 1;
    }
}

/* Sort NFILES FILES onto OUTPUT_FILE.  Use at most NTHREADS threads.  */

static void sort(char *const *files, size_t nfiles, char const *output_file, size_t nthreads) {
    struct buffer buf = {0};
    size_t ntemps = 0;
    bool output_file_created = false;

    while (nfiles) {
        char const *temp_output;
        char const *file = *files;
        FILE *fp = xfopen(file, "r");
        FILE *tfp;

        size_t bytes_per_line = (nthreads > 1)
            ? (sizeof(struct line) << (size_t)(1 + ceil(log2(nthreads))))
            : (sizeof(struct line) * 3 / 2);

        if (!buf.alloc) {
            initbuf(&buf, bytes_per_line,
                    sort_buffer_size(&fp, 1, files, nfiles, bytes_per_line));
        }

        buf.eof = false;
        files++;
        nfiles--;

        while (fillbuf(&buf, fp, file)) {
            struct line *line;

            if (buf.eof && nfiles &&
                (bytes_per_line + 1 < (buf.alloc - buf.used - bytes_per_line * buf.nlines))) {
                buf.left = buf.used;
                break;
            }

            line = buffer_linelim(&buf);

            if (buf.eof && !nfiles && !ntemps && !buf.left) {
                xfclose(fp, file);
                tfp = xfopen(output_file, "w");
                temp_output = output_file;
                output_file_created = true;
            } else {
                ++ntemps;
                temp_output = create_temp(&tfp)->name;
            }

            if (buf.nlines > 1) {
                struct merge_node_queue queue;
                queue_init(&queue, nthreads);
                struct merge_node *merge_tree = merge_tree_init(nthreads, buf.nlines, line);

                sortlines(line, nthreads, buf.nlines, merge_tree + 1, &queue, tfp, temp_output);

                merge_tree_destroy(nthreads, merge_tree);
                queue_destroy(&queue);
            } else {
                write_unique(line - 1, tfp, temp_output);
            }

            xfclose(tfp, temp_output);

            if (output_file_created) {
                goto finish;
            }
        }
        xfclose(fp, file);
    }

finish:
    free(buf.buf);

    if (!output_file_created) {
        struct tempnode *node = temphead;
        struct sortfile *tempfiles = xnmalloc(ntemps, sizeof *tempfiles);
        for (size_t i = 0; node; i++) {
            tempfiles[i].name = node->name;
            tempfiles[i].temp = node;
            node = node->next;
        }
        merge(tempfiles, ntemps, ntemps, output_file);
        free(tempfiles);
    }

    reap_all();
}

/* Insert a malloc'd copy of key KEY_ARG at the end of the key list.  */

#include <stdlib.h>
#include <string.h>

void insertkey(struct keyfield *key_arg) {
    if (key_arg == NULL) {
        return;
    }

    struct keyfield *key = malloc(sizeof *key);
    if (key == NULL) {
        return;
    }

    memcpy(key, key_arg, sizeof *key);

    if (keylist == NULL) {
        keylist = key;
        key->next = NULL;
        return;
    }

    struct keyfield *current = keylist;
    while (current->next != NULL) {
        current = current->next;
    }
    current->next = key;
    key->next = NULL;
}

/* Report a bad field specification SPEC, with extra info MSGID.  */

#include <stdio.h>
#include <errno.h>

void badfieldspec(const char *spec, const char *msgid) {
    if (!spec || !msgid) {
        fprintf(stderr, "Invalid input\n");
        return;
    }
    fprintf(stderr, "%s: invalid field specification %s\n", msgid, spec);
}

/* Report incompatible options.  */

#include <stdio.h>
#include <stdlib.h>

#define SORT_FAILURE 1

void error(int errnum, int dummy, const char *message, const char *opt) {
    fprintf(stderr, message, opt);
    fprintf(stderr, "\n");
    exit(errnum);
}

static void incompatible_options(const char *opts) {
    if (opts == NULL) {
        fprintf(stderr, "Invalid option.\n");
        exit(SORT_FAILURE);
    }
    error(SORT_FAILURE, 0, "options '-%s' are incompatible", opts);
}

/* Check compatibility of ordering options.  */

void check_ordering_compatibility(void) {
    for (struct keyfield *key = keylist; key; key = key->next) {
        int option_count = key->numeric + key->general_numeric + key->human_numeric
                           + key->month + key->version + key->random + (key->ignore != 0);
        
        if (option_count > 1) {
            char opts[sizeof(short_options)];
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

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

static char const *
parse_field_count (char const *string, size_t *val, char const *msgid)
{
  char *suffix;
  uintmax_t n;

  errno = 0;
  n = strtoumax(string, &suffix, 10);
  
  if (errno == 0 && *suffix != '\0') {
    errno = EINVAL;
  }

  if (errno == 0) {
    *val = (size_t)n;
    if (*val != n) {
      errno = ERANGE;
      *val = SIZE_MAX;
    }
  } else {
    switch (errno) {
      case ERANGE:
        *val = SIZE_MAX;
        break;
      case EINVAL:
      default:
        if (msgid) {
          fprintf(stderr, "%s: invalid count at start of %s\n", msgid, string);
        }
        return NULL;
    }
  }

  return suffix;
}

/* Handle interrupts and hangups. */

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

static void cleanup(void);

static void sighandler(int sig) {
    if (!SA_NOCLDSTOP) {
        if (signal(sig, SIG_IGN) == SIG_ERR) {
            perror("Failed to ignore signal");
            exit(EXIT_FAILURE);
        }
    }

    cleanup();

    if (signal(sig, SIG_DFL) == SIG_ERR) {
        perror("Failed to reset signal to default");
        exit(EXIT_FAILURE);
    }

    if (raise(sig) != 0) {
        perror("Failed to raise signal");
        exit(EXIT_FAILURE);
    }
}

static void cleanup(void) {
    // Cleanup operations here
}

/* Set the ordering options for KEY specified in S.
   Return the address of the first character in S that
   is not a valid ordering option.
   BLANKTYPE is the kind of blanks that 'b' should skip. */

static char *set_ordering(const char *s, struct keyfield *key, enum blanktype blanktype) {
  while (*s) {
    switch (*s) {
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
        if (!key->ignore) key->ignore = nonprinting;
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
        return (char *)s;
    }
    ++s;
  }
  return (char *)s;
}

/* Initialize KEY.  */

#include <stddef.h>
#include <limits.h>
#include <string.h>

static struct keyfield {
    size_t eword;
} *key_init(struct keyfield *key) {
    if (key == NULL) {
        return NULL;
    }
    memset(key, 0, sizeof(struct keyfield));
    key->eword = SIZE_MAX;
    return key;
}

```c
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include <getopt.h>
#include <locale.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <error.h>

#define SORT_FAILURE 2
#define MIN_SORT_SIZE 1024 * 1024 * 16 // 16 MiB
#define DEFAULT_MAX_THREADS 8

struct keyfield {
    size_t sword;
    size_t schar;
    size_t eword;
    size_t echar;
    bool reverse;
    bool ignore;
    bool translate;
    bool skipsblanks;
    bool skipeblanks;
    bool month;
    bool numeric;
    bool general_numeric;
    bool human_numeric;
    bool version;
    bool random;
    bool traditional_used;
};

void initialize_main(int *argc, char ***argv);
void set_program_name(const char *name);
void initialize_exit_failure(int sort_failure);
bool hard_locale(int category);
void inittables(void);
void key_init(struct keyfield *key);
bool set_ordering(const char *s, struct keyfield *key, int flags);
void insertkey(struct keyfield *key);
bool default_key_compare(struct keyfield *key);
bool check_ordering_compatibility(void);
void random_md5_state_init(const char *random_source);
void add_temp_dir(const char *dir);
void xnmalloc(size_t argc, size_t size);
void check_inputs(char **files, size_t nfiles);
void check_output(const char *outfile);
void merge(struct sortfile *sortfiles, size_t start, size_t nfiles, const char *outfile);
void sort(char **files, size_t nfiles, const char *outfile, size_t nthreads);

int main(int argc, char **argv) {
    struct keyfield *key;
    struct keyfield key_buf;
    struct keyfield gkey;
    char const *s;
    int c = 0;
    char checkonly = 0;
    char *random_source = NULL;
    bool need_random = false;
    size_t nthreads = 0;
    size_t nfiles = 0;
    char **files = NULL;
    char *files_from = NULL;
    char const *outfile = NULL;
    bool locale_ok;

    initialize_main(&argc, &argv);
    set_program_name(argv[0]);
    locale_ok = !!setlocale(LC_ALL, "");
    initialize_exit_failure(SORT_FAILURE);

    hard_LC_COLLATE = hard_locale(LC_COLLATE);

    decimal_point = '.';
    thousands_sep = NON_CHAR;

    have_read_stdin = false;
    inittables();
    sigset_t caught_signals;
    sigemptyset(&caught_signals);
    
    struct sigaction act;
    act.sa_handler = sighandler;
    act.sa_mask = caught_signals;
    act.sa_flags = 0;

    size_t i;
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

    for (i = 0; i < sizeof(sig) / sizeof(sig[0]); i++) {
        sigaction(sig[i], NULL, &act);
        if (act.sa_handler != SIG_IGN) {
            sigaddset(&caught_signals, sig[i]);
            sigaction(sig[i], &act, NULL);
        }
    }
    signal(SIGCHLD, SIG_DFL);
    atexit(exit_cleanup);
    key_init(&gkey);
    gkey.sword = SIZE_MAX;
    files = xnmalloc(argc, sizeof *files);

    while (true) {
        if ((c = getopt_long(argc, argv, short_options, long_options, NULL)) == -1) {
            if (argc <= optind) break;
            files[nfiles++] = argv[optind++];
        }
        switch (c) {
        case 1:
            if (optarg[0] == '+') { 
                bool minus_pos_usage = (optind != argc && argv[optind][0] == '-' && c_isdigit(argv[optind][1]));
                if (minus_pos_usage && !posixly_correct) {
                    /* Treat +POS1 [-POS2] as a key if possible; but silently
                       treat an operand as a file if it is not a valid +POS1.  */
                    key = key_init(&key_buf);
                    s = parse_field_count(optarg + 1, &key->sword, NULL);
                    if (s && *s == '.') s = parse_field_count(s + 1, &key->schar, NULL);
                    if (!(key->sword || key->schar)) key->sword = SIZE_MAX;
                    if (!s || *set_ordering(s, key, bl_start)) key = NULL;
                    else {
                        char const *optarg1 = argv[optind++];
                        s = parse_field_count(optarg1 + 1, &key->eword, N_("invalid number after '-'"));
                        if (*s == '.') s = parse_field_count(s + 1, &key->echar, N_("invalid number after '.'"));
                        if (!key->echar && key->eword) key->eword--;
                        if (*set_ordering(s, key, bl_end)) badfieldspec(optarg1, N_("stray character in field spec"));
                        key->traditional_used = true;
                        insertkey(key);
                    }
                }
            }
            if (!key) files[nfiles++] = optarg;
            break;

        case SORT_OPTION:
            c = XARGMATCH("--sort", optarg, sort_args, sort_types);
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
                char str[2] = {c, '\0'};
                set_ordering(str, &gkey, bl_both);
            }
            break;
        case CHECK_OPTION:
            c = (optarg ? XARGMATCH("--check", optarg, check_args, check_types) : 'c');
            FALLTHROUGH;
        case 'c':
        case 'C':
            if (checkonly && checkonly != c) incompatible_options("cC");
            checkonly = c;
            break;
        case COMPRESS_PROGRAM_OPTION:
            if (compress_program && !STREQ(compress_program, optarg))
                error(SORT_FAILURE, 0, _("multiple compress programs specified"));
            compress_program = optarg;
            break;
        case DEBUG_PROGRAM_OPTION:
            debug = true;
            break;
        case FILES0_FROM_OPTION:
            files_from = optarg;
            break;
        case 'k':
            key = key_init(&key_buf);
            s = parse_field_count(optarg, &key->sword, N_("invalid number at field start"));
            if (!key->sword--) badfieldspec(optarg, N_("field number is zero"));
            if (*s == '.') {
                s = parse_field_count(s + 1, &key->schar, N_("invalid number after '.'"));
                if (!key->schar--) badfieldspec(optarg, N_("character offset is zero"));
            }
            if (!(key->sword || key->schar)) key->sword = SIZE_MAX;
            s = set_ordering(s, key, bl_start);
            if (*s != ',') {
                key->eword = SIZE_MAX;
                key->echar = 0;
            } else {
                s = parse_field_count(s + 1, &key->eword, N_("invalid number after ','"));
                if (!key->eword--) badfieldspec(optarg, N_("field number is zero"));
                if (*s == '.') s = parse_field_count(s + 1, &key->echar, N_("invalid number after '.'"));
                s = set_ordering(s, key, bl_end);
            }
            if (*s) badfieldspec(optarg, N_("stray character in field spec"));
            insertkey(key);
            break;
        case 'm':
            mergeonly = true;
            break;
        case NMERGE_OPTION:
            specify_nmerge(0, c, optarg);
            break;
        case 'o':
            if (outfile && !STREQ(outfile, optarg))
                error(SORT_FAILURE, 0, _("multiple output files specified"));
            outfile = optarg;
            break;
        case RANDOM_SOURCE_OPTION:
            if (random_source && !STREQ(random_source, optarg))
                error(SORT_FAILURE, 0, _("multiple random sources specified"));
            random_source = optarg;
            break;
        case 's':
            stable = true;
            break;
        case 'S':
            specify_sort_size(0, c, optarg);
            break;
        case 't':
            if (!*optarg || (tab != TAB_DEFAULT && tab != *optarg)) 
                error(SORT_FAILURE, 0, _("incompatible tabs"));
            tab = *optarg;
            break;
        case 'T':
            add_temp_dir(optarg);
            break;
        case PARALLEL_OPTION:
            nthreads = specify_nthreads(0, c, optarg);
            break;
        case 'u':
            unique = true;
            break;
        case 'y':
            if (optarg == argv[optind - 1]) {
                char const *p;
                for (p = optarg; c_isdigit(*p); p++)
                    continue;
                optind -= (*p != '\0');
            }
            break;
        case 'z':
            eolchar = 0;
            break;

        default:
            usage(SORT_FAILURE);
        }
    }

    if (files_from) {
        if (nfiles) {
            error(0, 0, _("extra operand %s"), quoteaf(files[0]));
            fprintf(stderr, "%s\n", _("file operands cannot be combined with --files0-from"));
            usage(SORT_FAILURE);
        }
        FILE *stream = xfopen(files_from, "r");
        readtokens0_init(&tok);
        if (!readtokens0(stream, &tok))
            error(SORT_FAILURE, 0, _("cannot read file names from %s"), quoteaf(files_from));
        xfclose(stream, files_from);

        if (tok.n_tok) {
            free(files);
            files = tok.tok;
            nfiles = tok.n_tok;
            for (size_t i = 0; i < nfiles; i++) {
                if (STREQ(files[i], "-"))
                    error(SORT_FAILURE, 0, _("when reading file names from "
                                              "standard input, "
                                              "no file name of %s allowed"),
                          quoteaf(files[i]));
                else if (files[i][0] == '\0') {
                    unsigned long int file_number = i + 1;
                    error(SORT_FAILURE, 0,
                          _("%s:%lu: invalid zero-length file name"),
                          quotef(files_from), file_number);
                }
            }
        } else
            error(SORT_FAILURE, 0, _("no input from %s"), quoteaf(files_from));
    }

    for (key = keylist; key; key = key->next) {
        if (default_key_compare(key) && !key->reverse) {
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

    if (!keylist && !default_key_compare(&gkey)) {
        gkey_only = true;
        insertkey(&gkey);
        need_random |= gkey.random;
    }

    check_ordering_compatibility();
    if (debug) {
        if (checkonly || outfile) incompatible_options("X --debug");

        if (locale_ok) locale_ok = !!setlocale(LC_COLLATE, "");

        if (!locale_ok) error(0, 0, "%s", _("failed to set locale"));
        if (hard_LC_COLLATE)
            error(0, 0, _("text ordering performed using %s sorting rules"), quote(setlocale(LC_COLLATE, NULL)));
        else
            error(0, 0, "%s", _("text ordering performed using simple byte comparison"));

        key_warnings(&gkey, gkey_only);
    }

    reverse = gkey.reverse;
    if (need_random) random_md5_state_init(random_source);
    if (temp_dir_count == 0) {
        char const *tmp_dir = getenv("TMPDIR");
        add_temp_dir(tmp_dir ? tmp_dir : DEFAULT_TMPDIR);
    }

    if (nfiles == 0) {
        nfiles = 1;
        free(files);
        files = xmalloc(sizeof *files);
        *files = (char *) "-";
    }

    if (0 < sort_size) sort_size = MAX(sort_size, MIN_SORT_SIZE);

    if (checkonly) {
        if (nfiles > 1)
            error(SORT_FAILURE, 0, _("extra operand %s not allowed with -%c"), quoteaf(files[1]), checkonly);

        if (outfile) incompatible_options("options");

        exit(check(files[0], checkonly) ? EXIT_SUCCESS : SORT_OUT_OF_ORDER);
    }

    check_inputs(files, nfiles);
    check_output(outfile);

    if (mergeonly) {
        struct sortfile *sortfiles = xcalloc(nfiles, sizeof *sortfiles);
        for (size_t i = 0; i < nfiles; ++i) sortfiles[i].name = files[i];
        merge(sortfiles, 0, nfiles, outfile);
    } else {
        if (!nthreads) nthreads = MIN(num_processors(NPROC_CURRENT_OVERRIDABLE), DEFAULT_MAX_THREADS);
        size_t nthreads_max = SIZE_MAX / (2 * sizeof(struct merge_node));
        nthreads = MIN(nthreads, nthreads_max);
        sort(files, nfiles, outfile, nthreads);
    }

    if (have_read_stdin && fclose(stdin) == EOF) sort_die(_("close failed"), "-");
    main_exit(EXIT_SUCCESS);
}
```
