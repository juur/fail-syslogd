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
#include <sys/select.h>
#include <netdb.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/time.h>



#define MAX(a,b) ((a) > (b) ? (a) : (b))
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define LOG_NONE -2
#define LOG_ALL -3



typedef enum {
	TYPE_FILE   = 1,
	TYPE_REMOTE = 2,
	TYPE_USER   = 3,
	TYPE_OTHER  = 4
} target_t;

typedef enum {
    TYPE_LOCAL,
    TYPE_RFC3164,
    TYPE_RFC5424,
} format_t;



struct selector {
	int facility;
	int priority;
};

struct record {
	format_t type;
    int version;
    struct timeval tv;
    char *hostname;
    char *appname;
    char *procid;
    char *msgid;
    char *msg;
	int facility;
	int priority;
    /* TODO data */
};

struct entry {
    struct entry *next;

    target_t type;
    int      num_sel;
    bool     sync;

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

static regex_t main_line, comment_line, rfc5242_tz;
static int     log_fd;
static int     remote_fd;
static bool    running;
static time_t  last_mark;



/* 
 * group 1: selector_list
 * group 2: action
 * group 3: comment (ignored)
 *
 */
static const char main_line_re[]     = "^[[:space:]]*([0-9A-Za-z,!=*;.]+);?[[:space:]]+([-:*_0-9/@A-Za-z.]+)[[:space:]]*(#.*)?$";
static const char comment_line_re[]  = "^[[:space:]]*#.*$";
static const char rfc5242_tz_re[]    = "^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\\.([0-9]{1,6})((Z)|([+-][0-9]{2}:[0-9]{2}))$";

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

static const char *const record_types[] = {
	[TYPE_LOCAL]   = "TYPE_LOCAL",
	[TYPE_RFC3164] = "TYPE_RFC3164",
	[TYPE_RFC5424] = "TYPE_RFC5424",
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

static const char *get_pri_name(int pri)
{
	for (int i = 0; priority_names[i].name; i++)
		if (priority_names[i].priority == pri)
			return priority_names[i].name;

	return "UNDEFINED";
}

static const char *get_fac_name(int fac)
{
	for (int i = 0; facility_names[i].name; i++)
		if (facility_names[i].facility == fac)
			return facility_names[i].name;

	return "UNDEFINED";
}


static void print_record(FILE *to, const struct record *r)
{
	fprintf(to, 
			"type=[%s] facility=%s[%02d] priority=%s[%02d] version=%02d tv=%lu.%06lu "
			"hostname=<%s> appname=<%s> procid=<%s> msgid=<%s> msg=<%s>",
			record_types[r->type],
			get_fac_name(r->facility), r->facility,
			get_pri_name(r->priority), r->priority,
			r->version,
			r->tv.tv_sec,
			r->tv.tv_usec,
			r->hostname ? r->hostname : "",
			r->appname ? r->appname : "",
			r->procid ? r->procid : "",
			r->msgid ? r->msgid : "",
			r->msg ? r->msg : ""
		   );
}

__attribute__((nonnull))
static void send_log(struct entry *ent, const struct record *record)
{
    int    rc;
    size_t len;
    int    times;

	char   buf[BUFSIZ];

    struct tm   *tm;
    struct stat  sb;

	if (opt_debug) {
		printf("DEBUG: send_log: record: ");
		print_record(stdout, record);
		printf("\n");
	}

	if ((tm = localtime(&record->tv.tv_sec)) == NULL)
		err(EXIT_FAILURE, "send_log: localtime(%lu)", record->tv.tv_sec);
	
	len = sizeof(buf) - 1;
    times = 0;

    switch (ent->type)
    {
        case TYPE_USER:
            break;

        case TYPE_FILE:
			/* Mmm dd HH:MM:SS hostname appname[procid]: msg */

			/* Timestamp */
			len -= strftime(buf, 17, "%b %e %T ", tm);

			/* Hostname */
			len -= snprintf(buf + strlen(buf), len, "%s ", record->hostname ? record->hostname : "-");

			/* Appname */
			if (record->appname) {
				if (record->procid)
					/* procid, if present */
					len -= snprintf(buf + strlen(buf), len, "%s[%s]: ", record->appname, record->procid);
				else
					len -= snprintf(buf + strlen(buf), len, "%s: ", record->appname);
			}

			/* msgid is not logged to files typically on Linux */

			/* msg and trailing \n */
			if (record->msg)
				snprintf(buf + strlen(buf), len, "%s\n", record->msg);
again:
            if (ent->target.file.fd == -1) {
                if (times++) {
                    warn("send_log: too many attempts to open <%s>",
                            ent->target.file.name);
                    return;
                }

                if (opt_debug) printf("DEBUG: send_log: (re)opening <%s>\n",
                        ent->target.file.name);

                if ((ent->target.file.fd = open(ent->target.file.name, 
                                O_WRONLY|O_APPEND|O_CREAT|O_NOCTTY, 
                                S_IWUSR|S_IRUSR)) == -1) {
                    warn("send_log: open: <%s>:", ent->target.file.name);
                    goto again;
				}
			}

            if ((rc = fstat(ent->target.file.fd, &sb)) == -1) {
                warn("send_log: fstat: <%s>:", ent->target.file.name);
                goto barf;
            }

            if (sb.st_nlink == 0) {
                warnx("send_log: was closed: <%s>", ent->target.file.name);
                goto barf;
            }

			if ((rc = write(ent->target.file.fd, buf, strlen(buf))) == -1) {
				warn("send_log: write: <%s>:", ent->target.file.name);
barf:
				close(ent->target.file.fd);
				ent->target.file.fd = -1;
                goto again;
			}

			if (ent->sync)
				fdatasync(ent->target.file.fd);
				
			break;
		
		case TYPE_OTHER:
            if (opt_debug) printf("DEBUG: send_log: TYPE_OTHER\n");
			return send_log(ent->target.other, record);
		
		case TYPE_REMOTE:
			break;
		
		default:
			warnx("send_log: unknown TYPE: %d", ent->type);
	}
}

__attribute__((nonnull))
static void free_record(struct record *r)
{
    if (r->hostname) free(r->hostname);
    if (r->appname) free(r->appname);
    if (r->procid) free(r->procid);
    if (r->msgid) free(r->msgid);
    if (r->msg) free(r->msg);
    free(r);
}

__attribute__((nonnull))
static void trim(char *str)
{
	int pos;

	pos = strlen(str) - 1;

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

static void clean_remote(void)
{
    if (remote_fd != -1) {
        if (opt_debug) printf("DEBUG: clean_remote: closing remote_fd\n");
        shutdown(remote_fd, SHUT_RDWR);
        close(remote_fd);
        remote_fd = -1;
    }
}

static void clean_log_fd(void)
{
	if (log_fd != -1) {
        if (opt_debug) printf("DEBUG: clean_remote: closing log_fd\n");
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
    if (opt_debug) printf("DEBUG: sigint: sig=%d\n", sig);

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

static inline void nonblock(int fd)
{
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
}

__attribute__((nonnull, warn_unused_result))
static int setup_unix_socket(const char *path)
{
	int ret = -1;

	struct sockaddr_un sun_log;

	memset(&sun_log, 0, sizeof(sun_log));
	sun_log.sun_family = AF_UNIX;
	strcpy(sun_log.sun_path, path /*opt_mainsock*/);
	unlink(sun_log.sun_path);

	if ((ret = socket(AF_UNIX, SOCK_DGRAM, 0)) == -1)
		err(EXIT_FAILURE, "socket");

    nonblock(ret);

	if (bind(ret, (const struct sockaddr *)&sun_log, sizeof(sun_log)) == -1)
		err(EXIT_FAILURE, "bind");

	chmod(sun_log.sun_path, 0666);

    return ret;
}

__attribute__((nonnull, warn_unused_result))
static int setup_ip_socket(int port, int type)
{
    int ret = -1;

    struct sockaddr_in s_in;

    memset(&s_in, 0, sizeof(s_in));
    s_in.sin_family = AF_INET;
    s_in.sin_port   = htons(port);
    s_in.sin_addr.s_addr = htonl(INADDR_ANY);

    if ((ret = socket(AF_INET, type, 0)) == -1)
        err(EXIT_FAILURE, "setup_ip_socket: socket");

    nonblock(ret);

    if (bind(ret, (const struct sockaddr *)&s_in, sizeof(s_in)) == -1)
        err(EXIT_FAILURE, "setup_ip_socket: bind");

    if (type == SOCK_STREAM) {
        if (listen(ret, 5) == -1)
            err(EXIT_FAILURE, "setup_ip_socket: listen");
    }
    
    return ret;
}

__attribute__((nonnull))
static struct entry *find_match(struct entry *entries, int fac, int pri, bool any __attribute__((unused)))
{
	bool found;

	struct entry    *ent;
	struct selector *sel;

	ent = entries;

	//if (opt_debug) printf("DEBUG: find_match(%p)\n", entries);

	while (ent)
	{
		found = false;

		for (int i = 0; i < ent->num_sel; i++)
		{
			sel = &ent->selectors[i];

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
static void process_record(struct entry *entries, char *string, format_t format)
{
	char  *ptr;
	int    facility, priority;
	time_t now;
	char   hostname[64 + 1];

	struct entry *match, *start;
	struct record *record;

	if (opt_debug) printf("DEBUG: process_record(%p, <>)\n", entries);

	now      = time(NULL);
	ptr      = string;
	facility = LOG_USER;
	priority = LOG_NOTICE;
	record   = NULL;

	gethostname(hostname, sizeof(hostname));

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
	} else {
        warnx("process_record: malformed line: <%s>", string);
		goto bad_fmt;
	}

	start = entries;

	if ((record = calloc(1, sizeof(struct record))) == NULL)
		err(EXIT_FAILURE, "process_record: calloc(record)");

	record->facility = facility;
	record->priority = priority;

    /* mmm dd HH:MM:SS .+: */
    if (format != TYPE_RFC5424) {
		/* TODO confirm LOCAL vs RFC3542 */
		record->type = TYPE_RFC3164;

		time_t  event;
		char   *tmp;

        if (!(ptr[3] == ' ' && ptr[6] == ' ' && ptr[9] == ':' 
                    && ptr[12] == ':' && ptr[15] == ' ')) {
			gettimeofday(&record->tv, NULL);
		} else {
			struct tm tm, *local_tm;

			local_tm = localtime(&now);
			memcpy(&tm, local_tm, sizeof(struct tm));

			if ((tmp = strptime(ptr, "%b %e %H:%M:%S ", &tm)) != NULL) {
				event = mktime(&tm);
				record->tv.tv_sec = event;
				record->tv.tv_usec = 0;
				ptr = tmp;
			} else {
				gettimeofday(&record->tv, NULL);
			}
		}

		char *appname, *pid;
		int   rc;
		char  dummy1, dummy2;

		appname = NULL;
		pid = NULL;

		/* using a while(*ptr++) type approach might be better here? */
		if ((rc = sscanf(ptr, "%m[-_A-Z0-9a-z][%m[0-9]]%c%c", &appname, &pid, &dummy1, &dummy2)) == 4 
				&& dummy1 == ':' && dummy2 == ' ') {
			record->appname = appname;
			record->procid = pid;
			ptr = strchr(ptr, ':');
			ptr+= 2;
		} else {
			if (appname)
				free(appname);

			if (pid)
				free(pid);

			if ((rc = sscanf(ptr, "%m[-_A-Z0-9a-z]%c%c", &appname, &dummy1, &dummy2)) == 3
					&& dummy1 == ':' && dummy2 == ' ') {
				record->appname = appname;
				ptr = strchr(ptr, ':');
				ptr+= 2;
			} else if (appname) {
				free(appname);
			}
		}

		if ((record->hostname = strdup(hostname)) == NULL)
			err(EXIT_FAILURE, "process_record: strdup(hostname)");

		if ((record->msg = strdup(ptr)) == NULL)
			err(EXIT_FAILURE, "process_record: strdup(ptr)");

		if (opt_debug) {
			printf("DEBUG: process_record: TYPE_RFC3164: ");
			print_record(stdout, record);
			printf("\n");
		}

	} else { 
		/* RFC5424 formatted */
		record->type = TYPE_RFC5424;

		char *date, *data, *tok;

		char       tmp[BUFSIZ];
		regmatch_t pmatch[12];

		if ((tok = strtok(ptr, " ")) == NULL) 
			goto bad_fmt;

		record->version = atoi(tok);

		if (record->version != 1)
			goto bad_fmt;

		if ((tok = strtok(NULL, " ")) == NULL) 
			goto bad_fmt;

		if ((date = strdup(tok)) == NULL)
			err(EXIT_FAILURE, "process_record: strdup(date)");

		if (regexec(&rfc5242_tz, date, sizeof(pmatch)/sizeof(regmatch_t), pmatch, 0) == 0) {
			struct tm tm;
			int ms;

			sscanf(date, "%04u-%02u-%02uT%02u:%02u:%02u.%u",
					&tm.tm_year,
					&tm.tm_mon,
					&tm.tm_mday,
					&tm.tm_hour,
					&tm.tm_min,
					&tm.tm_sec,
					&ms);

			tm.tm_year -= 1900;
			tm.tm_mon -= 1;

			time_t event = mktime(&tm);

			if (pmatch[10].rm_so && pmatch[10].rm_eo) {
				int len =  pmatch[10].rm_eo - pmatch[10].rm_so;
				char c;
				int hr,min;

				strncpy(tmp, date + pmatch[10].rm_so, len);
				sscanf(tmp, "%c%02u:%02u", &c, &hr, &min); /* TODO error */

				min += (hr * 60);
				if (c == '-')
					min = -min;

				event -= (min * 60);
			} 

			record->tv.tv_sec = event;
			record->tv.tv_usec = ms;

			printf("date=<%s> => event=%lu.%06lu\n", 
					date, 
                    record->tv.tv_sec, 
                    record->tv.tv_usec);

			free(date);
        } else {
            printf("regexec failed <%s>\n", date);
			free(date);
			/* TODO barf */
		}

        if ((tok = strtok(NULL, " ")) == NULL) 
			goto bad_fmt;

		if (*tok && strcmp(tok, "-"))
			if ((record->hostname = strdup(tok)) == NULL)
				err(EXIT_FAILURE, "process_record: strdup(hostname)");

        if ((tok = strtok(NULL, " ")) == NULL) 
			goto bad_fmt;

		if (*tok && strcmp(tok, "-"))
			if ((record->appname = strdup(tok)) == NULL)
				err(EXIT_FAILURE, "process_record: strdup(appname)");

		if ((tok = strtok(NULL, " ")) == NULL) 
			goto bad_fmt;

		if (*tok && strcmp(tok, "-"))
			if ((record->procid = strdup(tok)) == NULL)
				err(EXIT_FAILURE, "process_record: strdup(procid)");

		if ((tok = strtok(NULL, " ")) == NULL) 
			goto bad_fmt;

		if (*tok && strcmp(tok, "-"))
			if ((record->msgid = strdup(tok)) == NULL)
				err(EXIT_FAILURE, "process_record: strdup(msgid)");

		if ((tok = strtok(NULL, "]")) == NULL) 
			goto bad_fmt;
        if (*(tok++) != '[') 
			goto bad_fmt;

        if ((data = strdup(tok)) == NULL)
			err(EXIT_FAILURE, "process_record: strdup(data)");
        free(data);

        if ((tok = strtok(NULL, "\0")) != NULL && *tok != '\0') {
            if (*(tok++) != ' ') 
				goto bad_fmt;

            if ((record->msg = strdup(tok)) == NULL)
				err(EXIT_FAILURE, "process_record: strdup(hostname)");
        } else
            record->msg = NULL;

    }

    do {
        if ((match = find_match(start, facility, priority, false)) == NULL
                /* TODO && (match = find_match(start, facility, priority, true)) == NULL */
           )
            return;

        start = match->next;

        if (opt_debug) 
            printf("DEBUG: process_record: target=[%s]<%s>\n", 
                    target_type[match->type],
                    (match->type == TYPE_FILE) ? match->target.file.name : "");


		/* TODO check record.msg is set! */
        send_log(match, record);

    } while(match && start);

	if (record)
		free_record(record);
    return;

bad_fmt:
    errx(EXIT_FAILURE, "process_record: bad format");
	if (record)
		free_record(record);
    return;
}

    __attribute__((nonnull))
static void main_loop(struct entry *entries)
{
    fd_set input_fd, exc_fd;
    int max_fd, rc;
    char buf[BUFSIZ];

    const int fds[] = {
        [0] = log_fd,
        [1] = opt_remote ? remote_fd : -1,
        [2] = -1,
    };

    const int num_fds = sizeof(fds) / sizeof(int);

    /* the actual main loop */
    while (running)
    {
        FD_ZERO(&input_fd);
        FD_ZERO(&exc_fd);

        /* populate the fd_sets */
        for (int i = max_fd = 0; i < num_fds; i++)
        {
            if (fds[i] == -1)
                continue;

            FD_SET(fds[i], &input_fd);
            FD_SET(fds[i], &exc_fd);

            max_fd = MAX(max_fd, fds[i]);
        }

        struct timeval tv = {
            .tv_sec  = 0,
            .tv_usec = 1000,
        };

        errno = 0;

        rc = select(max_fd + 1, &input_fd, NULL, &exc_fd, &tv);

        if (rc == -1 && errno != EINTR) {
            warn("select");
            running = false;
            continue;
        } else if (rc == -1 || rc == 0) /* includes EINTR */
            continue;

        /* check each socket */
        for (int i = 0; i < num_fds; i++)
        {
            socklen_t sa_len;
            socklen_t so_type_len;
            int       so_type;

            struct sockaddr_in sa;

            if (fds[i] == -1)
                continue;

            /* determine the socket type */

            sa_len = sizeof(sa);
            so_type_len = sizeof(so_type);

            if (getsockname(fds[i], (struct sockaddr *)&sa, &sa_len) == -1)
                err(EXIT_FAILURE, "main_loop: getsockname");

            if (getsockopt(fds[i], SOL_SOCKET, SO_TYPE, &so_type, &so_type_len) == -1)
                err(EXIT_FAILURE, "main_loop: getsockopt");

            /* TODO UNIX or UDP in this state: do we care? */
            if (FD_ISSET(fds[i], &exc_fd)) {
                if (opt_debug) printf("DEBUG: main_loop: fds[%d] is in exc_fd\n", i);
            }

            if (FD_ISSET(fds[i], &input_fd)) {
                const char *name;
                format_t format;

                if (sa.sin_family == AF_INET && so_type == SOCK_DGRAM) {
                    sa_len = sizeof(sa);

                    rc = recvfrom(remote_fd, buf, sizeof(buf) - 1, 0, 
                            (struct sockaddr *)&sa, &sa_len);
                    name = inet_ntoa(sa.sin_addr);
                    format = TYPE_RFC5424;
                } else if (sa.sin_family == AF_UNIX && so_type == SOCK_DGRAM) {
                    rc = read(log_fd, buf, sizeof(buf) - 1);
                    name = "-";
                    format = TYPE_LOCAL;
                } else {
                    /* TODO should this error? */
                    name = "UNKNOWN";
                    continue;
                }

                if (rc == -1 && errno != EINTR) {
                    warn("main_loop: read");
                    running = false;
                    continue;
                } else if (rc == -1) { /* EINTR */
                    continue;
                } else if (rc == 0) { /* timeout */
                    warnx("main_loop: read: NULL");
                    continue;
                }

                if (opt_debug) printf("DEBUG: main_loop: from [%s]\n", name);

                /* find the first non-null/non newline, and append a newline */
                rc--;

                while(rc && (buf[rc] == '\0' || buf[rc] == '\n')) 
                    rc--;

                buf[++rc] = '\0';

                process_record(entries, buf, format);
        running = false;

            }
        }

    }
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
    if (opt_debug) printf("DEBUG: daemon: setting up main UNIX socket\n");
    log_fd = setup_unix_socket(opt_mainsock);
    atexit(clean_log_fd);

    if (opt_remote) {
        if (opt_debug) printf("DEBUG: daemon: setting up main remote socket\n");
        struct servent *ent;
        int port = 514;

        if ((ent = getservbyname("syslog", "udp")) != NULL)
            port = ent->s_port;

        if (getuid() != 0/* && opt_debug*/)
            port += 1000;

        remote_fd = setup_ip_socket(port, SOCK_DGRAM);
        atexit(clean_remote);
    }

    if (opt_debug) printf("DEBUG: daemon: entering main loop\n");
    running = true;

    last_mark = time(NULL);
    if (opt_interval)
        alarm((opt_interval * 60));

    main_loop(entries);

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

            if (tmp) /* TODO: is this an error/can it even occur? */
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
                    free(tmp->target.file.name);
                    tmp->target.file.name = NULL;
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

                    free(tmp->target.remote.name);
                    tmp->target.remote.name = NULL;
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

    if ((rc = regcomp(&rfc5242_tz, rfc5242_tz_re, REG_EXTENDED)) != 0) {
        regerror(rc, &rfc5242_tz, errbuf, sizeof(errbuf));
		errx(EXIT_FAILURE, "regcomp: rfc5242_tz: %s", errbuf);
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
	regfree(&rfc5242_tz);

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
