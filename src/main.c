#define _XOPEN_SOURCE 700

#include "config.h"

#include <stdlib.h>
#include <syslog.h>
#include <err.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <strings.h>
#include <regex.h>
#include <stdbool.h>
#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <time.h>
#include <errno.h>



#define LOG_NONE -2
#define LOG_ALL -3

#define TYPE_FILE 1
#define TYPE_REMOTE 2
#define TYPE_USER 3
#define TYPE_OTHER 4



static bool   opt_debug       = false;
static bool   opt_forward     = false;
static bool   opt_background  = true;
static bool   opt_remote      = false;
static int    opt_verbose     = 0;
static bool   opt_rdns        = true;
__attribute__((unused))
static int    opt_num_sockets = 0; 
static int    opt_interval    = 20;

static const char  *opt_config      = NULL;
static const char  *opt_hostlist    = NULL;
static const char  *opt_domainlist  = NULL;
static const char  *opt_mainsock    = NULL;

__attribute__((unused))
static       char *const*opt_sockets     = NULL;

static regex_t main_line, comment_line;
static int     log_fd;
static bool    running;
static time_t  last_mark;



/* 
 * group 1: selector_list
 * group 2: action
 * group 3: comment (ignored)
 *
 */
static const char main_line_re[]     = "^\\s*([0-9A-Za-z,!=*;.]+);?\\s+([-:*_0-9/@A-Za-z.]+)\\s*(#.*)?$";
static const char comment_line_re[]  = "^\\s*#.*$";

static const char default_mainsock[] = "/tmp/log";
static const char default_config[]   = "syslogd.conf";

static const struct { 
    const char *const name; 
    const int facility;
} facility_names[] = {
	{"auth"     , LOG_AUTH     },
	{"authpriv" , LOG_AUTHPRIV },
	{"cron"     , LOG_CRON     },
	{"daemon"   , LOG_DAEMON   },
	{"kern"     , LOG_KERN     },
	{"lpr"      , LOG_LPR      },
	{"mail"     , LOG_MAIL     },
	{"news"     , LOG_NEWS     },
	{"syslog"   , LOG_SYSLOG   },
	{"user"     , LOG_USER     },
	{"uucp"     , LOG_UUCP     },
	{"local0"   , LOG_LOCAL0   },
	{"local1"   , LOG_LOCAL1   },
	{"local2"   , LOG_LOCAL2   },
	{"local3"   , LOG_LOCAL3   },
	{"local4"   , LOG_LOCAL4   },
	{"local5"   , LOG_LOCAL5   },
	{"local6"   , LOG_LOCAL6   },
	{"local7"   , LOG_LOCAL7   },

	{"*"        , LOG_ALL      },

	{NULL       , -1           } 
};

static const struct { 
    const char *const name; 
    const int priority;
} priority_names[] = {
	{"debug"   , LOG_DEBUG   },
	{"info"    , LOG_INFO    },
	{"notice"  , LOG_NOTICE  },
	{"warning" , LOG_WARNING },
	{"err"     , LOG_ERR     },
	{"crit"    , LOG_CRIT    },
	{"alert"   , LOG_ALERT   },
	{"emerg"   , LOG_EMERG   },
	{"none"    , LOG_NONE    },

	{"*"       , LOG_ALL     },

	{NULL      , -1          } 
};

static const char *const target_type[] = {
	[TYPE_FILE]   = "TYPE_FILE",
	[TYPE_OTHER]  = "TYPE_OTHER",
	[TYPE_REMOTE] = "TYPE_REMOTE",
	[TYPE_USER]   = "TYPE_USER",
};



struct selector {
	int facility;
	int priority;
};

struct entry {
	struct entry *next;

	int type;
	int num_sel;
	bool sync;

	union {
		struct {
			char *name;
			int   fd;
		} file;
		struct {
			char *name;
			int   fd;
			int   protocol;
		} remote;
		char **user_list;
		struct entry *other;
	} target;

	struct selector selectors[];
};

/* parsing:
 *
 * if the line ends in \, then merge with following line (repeat)
 * if the line matches comment_line_re regex, ignore
 * apply the main_line_re regex
 * split selector_list on ";" to get each selector
 * split selector on "." to get facility_list and priority
 * split facility_list on "," to get each facility
 * facility is a keyword or "*"
 * priority may start with !=, = or !
 * priority is a keyword or "none"
 * action is parsed thus:
 * files begin with "/"
 * named pipes begin with "|"
 * remote hosts begin with "@"
 * otherwise a user_list which can be split on "," with "*" being all users
 */

static void send_log(struct entry *ent, const char *message, int fac, int pri)
{
	int rc;

	switch (ent->type)
	{
		case TYPE_USER:
			break;
		case TYPE_FILE:
			if (ent->target.file.fd == -1) {
				if ((ent->target.file.fd = open(ent->target.file.name, O_WRONLY|O_APPEND|O_CREAT|O_NOCTTY, S_IWUSR|S_IRUSR)) == -1) {
					warn("send_log: open: <%s>:", ent->target.file.name);
					return;
				}
			}

			if ((rc = write(ent->target.file.fd, message, strlen(message))) == -1) {
				warn("send_log: write: <%s>:", ent->target.file.name);
				close(ent->target.file.fd);
				ent->target.file.fd = -1;
				return;
			}

			if (ent->sync)
				fdatasync(ent->target.file.fd);
				
			break;
		case TYPE_OTHER:
			return send_log(ent->target.other, message, fac, pri);
		case TYPE_REMOTE:
			break;
		default:
			warnx("send_log: unknown TYPE");
	}
}

__attribute__((nonnull))
static void trim(char *str)
{
	int pos = strlen(str) - 1;

	while (pos && isspace(str[pos]))
		str[pos--] = '\0';
}

__attribute__((nonnull))
static int lookup_fac(const char *txt)
{
	for (int i = 0; facility_names[i].name; i++)
		if (!strcasecmp(txt, facility_names[i].name))
			return facility_names[i].facility;

	return -1;
}

__attribute__((nonnull))
static int lookup_pri(const char *txt)
{
	for (int i = 0; priority_names[i].name; i++)
		if (!strcasecmp(txt, priority_names[i].name))
			return priority_names[i].priority;

	return -1;
}

__attribute__((nonnull))
static void free_entries(struct entry *entries)
{
	for(struct entry *next, *tmp = entries; tmp;)
	{
		next = tmp->next;

		switch (tmp->type)
		{
			case TYPE_FILE:
				free(tmp->target.file.name);
				break;
			case TYPE_REMOTE:
				free(tmp->target.remote.name);
				break;
			case TYPE_USER:
				/* TODO */
				break;
			case TYPE_OTHER:
				tmp->target.other = NULL;
				break;
			default:
				errx(EXIT_FAILURE, "unknown TYPE %d", tmp->type);
		}

		free(tmp);
		tmp = next;
	}
}

static void clean_pid(void)
{
	if (unlink("/tmp/syslog.pid") == -1)
		warn("unlink: syslog.pid");
}

static void clean_log_fd(void)
{
	if (log_fd != -1) {
		close(log_fd);
		unlink(opt_mainsock);
		log_fd = -1;
	}
}

static void sig_sigalrm(int sig, siginfo_t *info __attribute__((unused)), void *ucontext __attribute__((unused)))
{
	if (sig == SIGALRM) {
		if (opt_interval) {
			last_mark = time(NULL);
			alarm(opt_interval * 60);
		} else {
			/* ??? */
		}
	}
}

static void sig_sigchld(int sig, siginfo_t *info, void *ucontext __attribute__((unused)))
{
	int wstatus;

	if (sig == SIGCHLD)
		waitpid(info->si_pid, &wstatus, WNOHANG);
}

static void sig_sigint(int sig, siginfo_t *info __attribute__((unused)), void *ucontext __attribute__((unused)))
{
	if (sig == SIGINT)
		running = false;
}

static void setup_signals(void)
{
	sigset_t set, oldset;

	sigfillset(&set);
	sigdelset(&set, SIGALRM);
	sigdelset(&set, SIGINT);
	sigdelset(&set, SIGQUIT);
	sigdelset(&set, SIGTERM);
	sigdelset(&set, SIGTERM);
	sigdelset(&set, SIGUSR1);

	if (sigprocmask(SIG_BLOCK, &set, &oldset) == -1)
		warn("sigprocmask");

	const struct sigaction sigactions[] = {
		[SIGALRM] = { .sa_sigaction = sig_sigalrm, .sa_flags = SA_SIGINFO },
		[SIGCHLD] = { .sa_sigaction = sig_sigchld, .sa_flags = SA_SIGINFO },
		[SIGINT]  = { .sa_sigaction = sig_sigint,  .sa_flags = SA_SIGINFO },
		[SIGQUIT] = { .sa_handler   = SIG_DFL                             },
		[SIGTERM] = { .sa_handler   = SIG_DFL                             },
		[SIGUSR1] = { .sa_handler   = SIG_DFL                             },
	};

	const int sigactions_size = sizeof(sigactions) / sizeof(struct sigaction);

	for (int i = 0; i < sigactions_size; i++)
	{
		if (sigactions[i].sa_sigaction || sigactions[i].sa_flags)
			if (sigaction(i, &sigactions[i], NULL) == -1)
				warn("sigaction");
	}
}

static void setup_socket()
{
	log_fd = -1;

	struct sockaddr_un sun_log;

	memset(&sun_log, 0, sizeof(sun_log));
	sun_log.sun_family = AF_UNIX;
	strcpy(sun_log.sun_path, opt_mainsock);
	unlink(sun_log.sun_path);

	atexit(clean_log_fd);

	if ((log_fd = socket(AF_UNIX, SOCK_DGRAM, 0)) == -1)
		err(EXIT_FAILURE, "socket");

	if (bind(log_fd, (const struct sockaddr *)&sun_log, sizeof(sun_log)) == -1)
		err(EXIT_FAILURE, "bind");

	chmod(sun_log.sun_path, 0666);
}

__attribute__((nonnull))
static struct entry *find_match(struct entry *entries, int fac, int pri, bool any __attribute__((unused)))
{
	struct entry *ent;

	ent = entries;

	if (opt_debug) printf("DEBUG: find_match(%p)\n", entries);

	while (ent)
	{
		bool found = false;
		struct selector *sel;

		for (int i = 0; i < ent->num_sel; i++)
		{
			sel = &ent->selectors[i];

			if (opt_debug) printf("DEBUG: find_match: comparing %08x.%08x[%08x] with %08x.%08x\n", 
					pri, fac, (1 << fac),
					sel->priority, sel->facility);

			if (!(sel->priority & (1 << pri)))
				continue;
			if (!(sel->facility & (1 << fac)))
				continue;

			found = true;

			/* TODO check this logic works for 'any' and 'none' */
		}

		if (found)
			return ent;

		ent = ent->next;
	}

	return NULL;
}

__attribute__((nonnull))
static void process_record(struct entry *entries, char *string)
{
	char *ptr;
	int   facility, priority;
	bool  need_date;

	struct entry *match, *start;

	if (opt_debug) printf("DEBUG: process_record(%p, <%s>)\n", entries, string);

	ptr      = string;
	facility = LOG_USER;
	priority = LOG_NOTICE;

	if (*ptr == '<') {
		unsigned int tmp;

		/* Linux defines PRIMASK as 0x7 ((1<<3)-1) and FACMASK as 0x03f8 */

		if (sscanf(ptr, "<%u>", &tmp) == 1) {
			facility = (tmp & ~0x0007);
			priority = (tmp &  0x0007);
		}

		while (*ptr && *ptr != '>') 
			ptr++;

		if (*ptr) 
			ptr++;
	}

	start = entries;

	strcat(ptr, "\n");

	do {
		if ( (match = find_match(start, facility, priority, false)) == NULL &&
				(match = find_match(start, facility, priority, true)) == NULL )
			return;

		start = match->next;
		need_date = false;

		/* mmm dd HH:MM:SS .+: */
		if (!(ptr[3] == ' ' && ptr[6] == ' ' && ptr[9] == ':' && ptr[12] == ':' && ptr[15] == ' '))
			need_date = true;

		if (opt_debug) printf("DEBUG: process_record: fac=%d pri=%d m=<%s> need_date=%s target=[%s]<%s>\n", 
				facility, priority, ptr,
				need_date ? "true" : "false",
				target_type[match->type],
				(match->type == TYPE_FILE) ? match->target.file.name : "");


		send_log(match, ptr, facility, priority);

	} while(match && start);
}

__attribute__((nonnull))
static void daemon(struct entry *entries, int pipe_fd)
{
	pid_t child;
	char  buf;
	FILE *pid_file;

	if (opt_background) {

		setsid();

		if ((child = fork()) > 0) {
			free_entries(entries);
			exit(EXIT_SUCCESS);
		} else if (child == -1) {
			err(EXIT_FAILURE, "fork2");
		}

		/* real child from here */

		fclose(stdout);
		fclose(stdin);
		fclose(stderr);

		close(STDIN_FILENO);
		close(STDOUT_FILENO);
		close(STDERR_FILENO);


		open("/dev/null", O_RDONLY);
		/*
		   open("/dev/null", O_WRONLY);
		   open("/dev/null", O_WRONLY);
		   */
		open("/tmp/syslog.log", O_WRONLY|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR);
		open("/tmp/syslog.log", O_WRONLY|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR);

		stdout = fdopen(STDOUT_FILENO, "a");
		stderr = fdopen(STDERR_FILENO, "a");

		setvbuf(stdout, NULL, _IONBF, 0);
		setvbuf(stderr, NULL, _IONBF, 0);

		umask(0022);
		chdir("/");

		atexit(clean_pid);

		if ((pid_file = fopen("/tmp/syslog.pid","w")) != NULL) {
			fprintf(pid_file, "%d", getpid());
			fclose(pid_file);
		} else
			warn("fopen: syslog.pid");

		buf = 'X';
		if (write(pipe_fd, &buf, 1) == -1)
			err(EXIT_FAILURE, "write: pipe");
		close(pipe_fd);
	}

	/* daemon set-up successfully from here */

	if (opt_debug) printf("DEBUG: daemon: setting up signals\n");
	setup_signals();
	if (opt_debug) printf("DEBUG: daemon: setting up socket\n");
	setup_socket();

	if (opt_debug) printf("DEBUG: daemon: entering main loop\n");
	running = true;

	last_mark = time(NULL);
	if (opt_interval)
		alarm((opt_interval * 60));

	while (running)
	{
		char buf[BUFSIZ];
		int rc;

		errno = 0;
		memset(buf, 0, sizeof(buf));

		rc = read(log_fd, buf, sizeof(buf) - 1);

		if (rc == -1) {
			if (errno == EINTR)
				continue;
			warn("read");
			running = false;
			continue;
		} else if (rc == 0) {
			warnx("read: NULL");
			continue;
		}

		rc--;

		while(rc && (buf[rc] == '\0' || buf[rc] == '\n')) rc--;
		buf[++rc] = '\0';

		process_record(entries, buf);

		running = false;
	}


	if (opt_background) {
		free_entries(entries);
		exit(EXIT_SUCCESS);
	}
}


/* process a single line from the config file, broken lines with \ should already be
 * merged prior to calling */
__attribute__((nonnull))
static struct entry *process_line(char *one, const char *two)
{
	char *tmp;
	int sel_cnt = 1, fac_cnt = 0;
	char **selectors;
	struct entry *ent;

	/* count and split selectors on ; if present */

	for (tmp = one; *tmp; tmp++)
		if (*tmp == ';')
			sel_cnt++;

	if ( (selectors = calloc(1, sizeof(char *) * (sel_cnt + 1))) == NULL )
		err(EXIT_FAILURE, "calloc");

	if (sel_cnt > 1) {
		int i = 0;
		tmp = strtok(one, ";");
		selectors[i++] = tmp;

		while ((tmp = strtok(NULL, ";")) != NULL)
			selectors[i++] = tmp;
	} else {
		selectors[0] = one;
	}

	/* create entry structure to return */

	if ((ent = calloc(1, sizeof(struct entry) + (sizeof(struct selector) * (sel_cnt + 1)))) == NULL)
		err(EXIT_FAILURE, "calloc");

	ent->num_sel = sel_cnt;

	/* process target information */

	if (*two == '-') {
		ent->sync = false;
		two++;
	} else
		ent->sync = true;

	switch (*two)
	{
		case '/':
			ent->type = TYPE_FILE;
			ent->target.file.name = strdup(two);
			ent->target.file.fd   = -1;
			break;

		case '@':
			ent->type = TYPE_REMOTE;
			ent->target.remote.name = strdup(two + 1);
			ent->target.remote.fd   = -1;
			break;

		default:
			ent->type = TYPE_USER;
			/* TODO parse user list here */
			break;
	}

	/* process each selector */

	for (int i = 0; i < sel_cnt; i++ ) 
	{
		if (!strchr(selectors[i], '.')) {
			warnx("invalid selector: <%s>", selectors[i]);
			continue;
		}

		char *fac_list = NULL, *pri = NULL;

		/* process facilities_list */
		fac_list = strtok(selectors[i], ".");

		if (fac_list == NULL) {
			/* should never happen? */
			warnx("invalid selector: <%s>", selectors[i]);
			continue;
		}

		pri = strtok(NULL, ".");
		if (pri == NULL) {
			/* should never happen? */
			warnx("invalid selector: <%s>", selectors[i]);
			continue;
		}

		fac_cnt = 1;

		for (tmp = fac_list; *tmp; tmp++)
			if (*tmp == ',')
				fac_cnt++;

		int fac = 0;

		if (fac_cnt > 1) {
			tmp = strtok(fac_list, ",");

			if (!tmp) /* TODO: is this an error/can it even occur? */
				do {
					int tmp_fac = lookup_fac(tmp);
					if (tmp_fac == -1) {
						warnx("invalid facility: <%s>", tmp);
						goto skip;
					}
					fac |= (1 << tmp_fac);
				} while( (tmp = strtok(NULL, ",")) != NULL );

		} else { /* TODO: can the non , list case be merged ? */
			fac = lookup_fac(fac_list);

			if (fac == -1) {
				warnx("invalid facility: <%s>", fac_list);
				continue;
			}

			if (fac == LOG_ALL)
				fac = ~0;
			else
				fac = (1 << fac);
		}

		/* process priority */
		bool pri_negate = false;
		bool pri_equal  = false;

		if (*pri && *pri == '!') {
			pri_negate = true;
			pri++;
		}

		if (*pri && *pri == '=') {
			pri_equal = true;
			pri++;
		}

		int pri_num = lookup_pri(pri);

		if (pri_num == -1) {
			warnx("invalid priority: <%s>", pri);
			continue;
		}

		int priority = 0;

		if (pri_num == LOG_ALL)
			pri_num = LOG_DEBUG;

		/* TODO: What if ALL and = ? */

		if (pri_equal) /* equal, so just this priority */
			priority |= (1 << pri_num);
		else /* no-equal, so include all higher priorities*/
			for (int i = pri_num; i >= 0; i--)
				priority |= (1 << i);

		if (pri_negate)
			priority = ~priority;

		/* store priority and facility */
		ent->selectors[i].priority = priority;
		ent->selectors[i].facility = fac;
skip:
	}

	free(selectors);
	return ent;
}

__attribute__((nonnull))
static struct entry *parse_config(FILE *fp)
{
	char   linebuf[BUFSIZ];
	char  *bufptr = linebuf;
	size_t bufsiz;

	struct entry *ret = NULL;

	bufsiz = sizeof(linebuf) - 1;
	memset(linebuf, 0, sizeof(linebuf));

	/* file read loop */
	while (!feof(fp) || ! ferror(fp))
	{
		if (fgets(bufptr, bufsiz, fp) == NULL) {
			if (!feof(fp))
				warn("fgets");
			break;
		}

		trim(bufptr);
		bufsiz -= strlen(bufptr);

		/* handle the case where a line is split */
		if (bufptr[strlen(bufptr) - 1] == '\\') {
			bufptr += strlen(bufptr) - 2;
			bufsiz--;
			continue;
		}

		/* skip blank lines */
		if (strlen(linebuf) == 0)
			goto reset;

		/* skip comments */
		if (!regexec(&comment_line, linebuf, 0, NULL, 0))
			goto reset;

		regmatch_t pmatch[3];

		/* handle real lines */
		if (!regexec(&main_line, linebuf, 3, pmatch, 0)) {
			char *one, *two;

			one = strndup(linebuf + pmatch[1].rm_so, pmatch[1].rm_eo - pmatch[1].rm_so);
			two = strndup(linebuf + pmatch[2].rm_so, pmatch[2].rm_eo - pmatch[2].rm_so);

			if (one == NULL || two == NULL)
				err(EXIT_FAILURE, "strndup");

			struct entry *tmp = process_line(one, two);

			if (ret) 
				tmp->next = ret;
			ret = tmp;

			free(one);
			free(two);

			goto reset;
		}

		warnx("parse_config: illegal line: <%s>\n", linebuf);

reset:
		/* reset buffers etc. for another process */

		memset(linebuf, 0, sizeof(linebuf));
		bufsiz = sizeof(linebuf) - 1;
		bufptr = linebuf;
		continue;

	} /* file read loop*/

	return ret;
}

/* consolidate duplicate targets to single instances */
__attribute__((nonnull))
static void check_dupes(struct entry *ents)
{
	struct entry *cur;

	cur = ents;

	while (cur)
	{
		if (cur->type == TYPE_OTHER)
			goto skip;

		for (struct entry *tmp = cur->next; tmp; tmp = tmp->next)
		{
			if (tmp->type != cur->type)
				continue;

			switch (tmp->type)
			{
				case TYPE_FILE:
					if (strcmp(cur->target.file.name, tmp->target.file.name))
						continue;
					break;
				case TYPE_OTHER:
					continue;
				case TYPE_USER:
					/* TODO */
					continue;
				case TYPE_REMOTE:
					if (cur->target.remote.protocol != tmp->target.remote.protocol)
						continue;
					if (strcmp(cur->target.remote.name, tmp->target.remote.name))
						continue;
					break;
				default:
					warn("unknown TYPE in check_dupes");
					continue;
			}

			if (opt_debug) printf("DEBUG: check_dupes: de-duplicating\n");

			/* must have a match */
			tmp->type = TYPE_OTHER;
			tmp->target.other = cur;
		}
skip:
		cur = cur->next;
	}
}

static void show_version(void)
{
	fprintf(stderr, "syslogd version " VERSION "\n");
}

static void show_usage(void)
{
	show_version();
	fprintf(stderr, "Usage: syslogd [-dhnrSvx] [-a socket] [-f config_file] [-l hostlist] [-m interval] [-p socket] [-s domainlist]");
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	opt_mainsock = default_mainsock;
	opt_config   = default_config;

	{
		int opt;
		while ((opt = getopt(argc, argv, "dhnrSvxa:f:l:m:p:s:")) != -1)
		{
			switch (opt)
			{
				case 'd': opt_debug = true;       
						  /* fall-through */
				case 'n': opt_background = false; break;
				case 'h': opt_forward = true;     break;
				case 'r': opt_remote = true;      break;
				case 'S': opt_verbose++;          break;
				case 'x': opt_rdns = false;       break;

				case 'a': {
						  }
						  break;
				case 'f': opt_config = optarg;         break;
				case 'l': opt_hostlist = optarg;       break;
				case 'm': opt_interval = atoi(optarg); break;
				case 's': opt_domainlist = optarg;     break;
				case 'p': opt_mainsock = optarg;       break;

				case 'v':
						  show_version();
						  exit(EXIT_SUCCESS);
				default:
						  show_usage();
			}
		}
	}

	int   rc;
	int   filedes[2];
	char  buf;
	pid_t child;
	FILE *conf;
	char  errbuf[BUFSIZ];

	struct entry *entries;

	if ((rc = regcomp(&main_line, main_line_re, REG_EXTENDED|REG_ICASE)) != 0) {
		regerror(rc, &main_line, errbuf, sizeof(errbuf));
		errx(EXIT_FAILURE, "regcomp: main_line: %s", errbuf);
	}

	if ((rc = regcomp(&comment_line, comment_line_re, REG_EXTENDED|REG_ICASE)) != 0) {
		regerror(rc, &comment_line, errbuf, sizeof(errbuf));
		errx(EXIT_FAILURE, "regcomp: comment_line: %s", errbuf);
	}

	if (opt_debug) printf("DEBUG: main: opening config file <%s>\n", opt_config);

	if ((conf = fopen(opt_config, "r")) == NULL)
		err(EXIT_FAILURE, "fopen: %s", opt_config);

	if ((entries = parse_config(conf)) == NULL)
		exit(EXIT_FAILURE);

	fclose(conf);

	if (opt_debug) printf("DEBUG: main: checking for duplicate targets\n");
	check_dupes(entries);

	regfree(&main_line);
	regfree(&comment_line);

	if (opt_background) {
		if (opt_debug) printf("DEBUG: main: running in background\n");
		if (pipe(filedes) == -1)
			err(EXIT_FAILURE, "pipe");

		if ((child = fork()) == 0) {
			close(filedes[0]);
			daemon(entries, filedes[1]);
		}

		if (child == -1)
			err(EXIT_FAILURE, "fork");

		close(filedes[1]);
	} else {
		if (opt_debug) printf("DEBUG: main: running in foreground\n");
		daemon(entries, 0);
	}

	free_entries(entries);

	if (opt_background) {
		if ((read(filedes[0], &buf, 1)) == -1)
			err(EXIT_FAILURE, "read: pipe");

		close(filedes[0]);
	}

	if (opt_debug) printf("DEBUG: main: exiting\n");

	exit(EXIT_SUCCESS);
}
