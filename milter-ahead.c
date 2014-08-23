/*
 * milter-ahead.c
 *
 * Copyright 2004, 2010 by Anthony Howe. All rights reserved.
 *
 * The following should be added to the sendmail.mc file:
 *
 *	INPUT_MAIL_FILTER(
 *		`milter-ahead',
 *		`S=unix:/var/lib/milter-ahead.socket, T=C:1m;S:30s;R:6m;E:1m'
 *	)dnl
 */

/***********************************************************************
 *** Leave this header alone. Its generated from the configure script.
 ***********************************************************************/

#include "config.h"

/***********************************************************************
 *** You can change the stuff below if the configure script doesn't work.
 ***********************************************************************/

#ifndef RUN_AS_USER
#define RUN_AS_USER			"milter"
#endif

#ifndef RUN_AS_GROUP
#define RUN_AS_GROUP			"milter"
#endif

#ifndef MILTER_CF
#define MILTER_CF			"/etc/mail/" MILTER_NAME ".cf"
#endif

#ifndef PID_FILE
#define PID_FILE			"/var/run/milter/" MILTER_NAME ".pid"
#endif

#ifndef SOCKET_FILE
#define SOCKET_FILE			"/var/run/milter/" MILTER_NAME ".socket"
#endif

#ifndef WORK_DIR
#define WORK_DIR			"/var/tmp"
#endif

#ifndef CACHE_FILE
#define CACHE_FILE			"/var/cache/" MILTER_NAME ".db"
#endif

#ifndef SOCKET_TIMEOUT_QUIT
#define SOCKET_TIMEOUT_QUIT		5000
#endif

#define NON_BLOCKING_READ
#define NON_BLOCKING_WRITE

/***********************************************************************
 *** No configuration below this point.
 ***********************************************************************/

/* Re-assert this macro just in case. May cause a compiler warning. */
#define _REENTRANT	1

#include <com/snert/lib/version.h>

#include <pwd.h>
#include <grp.h>
#include <ctype.h>
#include <errno.h>
#include <time.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <unistd.h>
#include <netdb.h>
#include <sys/stat.h>

#ifdef __sun__
# define _POSIX_PTHREAD_SEMANTICS
#endif
#include <signal.h>

#if LIBSNERT_MAJOR < 1 || LIBSNERT_MINOR < 75
# error "LibSnert 1.75.8 or better is required"
#endif

# define MILTER_STRING	MILTER_NAME"/"MILTER_VERSION

#if ! defined(HAVE_GMTIME_R) || ! defined(HAVE_LOCALTIME_R)
# error "thread safe gmtime_r() and localtime_r() are required"
#endif

#include <com/snert/lib/crc/Luhn.h>
#include <com/snert/lib/mail/limits.h>
#include <com/snert/lib/mail/mf.h>
#include <com/snert/lib/mail/smf.h>
#include <com/snert/lib/mail/smdb.h>
#include <com/snert/lib/net/pdq.h>
#include <com/snert/lib/io/file.h>
#include <com/snert/lib/io/socket2.h>
#include <com/snert/lib/sys/sysexits.h>
#include <com/snert/lib/util/Cache.h>
#include <com/snert/lib/util/Text.h>
#include <com/snert/lib/util/setBitWord.h>

/***********************************************************************
 *** Constants
 ***********************************************************************/

#define HOP_INFO_FORMAT		"server %s for <%s> "
#define HOP_INFO_ARGS		rcpt_host, rcpt_addr

#define	TAG_FORMAT		"%05d %s: "
#define	TAG_ARGS		data->work.cid, data->work.qid

#ifndef DB_UNKNOWN
#define DB_UNKNOWN		DB_HASH
#endif

/***********************************************************************
 *** Global Variables
 ***********************************************************************/

static smfInfo milter;

typedef struct {
	time_t created;
	time_t touched;
	sfsistat status;
	unsigned long count;
	char reply[SMTP_REPLY_LINE_LENGTH];
} CacheEntry;

#define CACHE_SCANF_FORMAT	"%lx %lx %d %lu %s"
#define CACHE_SCANF_DOT(v)	(long *) &(v).created, (long *) &(v).touched, &(v).status, &(v).count, (v).reply
#define CACHE_SCANF_ARROW(v)	(long *) &(v)->created, (long *) &(v)->touched, &(v)->status, &(v)->count, (v)->reply

#define CACHE_PRINTF_FORMAT	"%lx %lx %d %lu '%s'"
#define CACHE_PRINTF_DOT(v)	(long) (v).created, (long) (v).touched, (v).status, (v).count, (v).reply
#define CACHE_PRINTF_ARROW(v)	(long) (v)->created, (long) (v)->touched, (v)->status, (v)->count, (v)->reply

static CacheEntry cacheUndefinedEntry = { 0, 0, X_SMFIS_UNKNOWN, 0, { 0 } };
static volatile Cache cache;

static smdb *callAheadDb;

typedef struct {
	smfWork work;
	Socket2 *server;			/* per RCPT */
	char line[SMTP_TEXT_LINE_LENGTH+1];	/* general purpose */
} *workspace;

static struct bitword isIpBits[] = {
	{ IS_IP_ANY,		"all" },
	{ IS_IP_BENCHMARK,	"benchmark" },
	{ IS_IP_LINK_LOCAL,	"link-local" },
	{ IS_IP_LOCALHOST,	"localhost" },
	{ IS_IP_LOOPBACK,	"loopback" },
	{ IS_IP_MULTICAST,	"multicast" },
	{ IS_IP_PROTOCOL,	"protocol" },
	{ IS_IP_PRIVATE_A,	"private-a" },
	{ IS_IP_PRIVATE_B,	"private-b" },
	{ IS_IP_PRIVATE_C,	"private-c" },
	{ IS_IP_V6_RESERVED,	"reserved" },
	{ IS_IP_TEST_NET_1,	"test-net-1" },
	{ IS_IP_TEST_NET_2,	"test-net-2" },
	{ IS_IP_TEST_NET_3,	"test-net-3" },
	{ IS_IP_THIS_NET,	"this-net" },
	{ 0, NULL }
};

static const char usage_backup_mx[] =
  "We are a backup MX or gateway and should accept mail when the\n"
"# down stream server is unreachable.\n"
"#"
;
static const char usage_primary_up_reject[] =
  "We are a backup MX and we want to reject mail when the primary\n"
"# MX is available. This does not conform with RFC 974 & 2821 mail\n"
"# routing, which only requires mail clients attempt delivery to the\n"
"# primary first, before trying other MXes.\n"
"#"
;
static const char usage_reserved_ip[] =
  "A comma or semi-colon separated word list of reserved IPs to reject:\n"
"#\n"
"#        all = all reserved IP\n"
"#  benchmark = 198.18.0.0/15                RFC 2544\n"
"# link-local = 169.254.0.0/16, FE80::/10    RFC 3330, 3513\n"
"#  localhost = 127.0.0.1, ::1               RFC 3330, 3513\n"
"#   loopback = 127.0.0.0/8                  excluding 127.0.0.1\n"
"#  multicast = 224.0.0.0/4, FF00::/8        RFC 3171\n"
"#  private-a = 10.0.0.0/8                   RFC 3330\n"
"#  private-b = 172.16.0.0/12                RFC 3330\n"
"#  private-c = 192.168.0.0/16               RFC 3330\n"
"#   reserved = IPv6 unassigned              RFC 3513\n"
"# site-local = FEC0::0/10                   RFC 3513\n"
"#   test-net = 192.0.2.0/24, 2001:DB8::/32  RFC 3330, 3849\n"
"#   this-net = 0.0.0.0/8, ::0               RFC 3330, 3513\n"
"#"
;
static const char usage_call_ahead_db[] =
  "Lookup recipient's domain for a call-ahead host from a Berkeley\n"
"# DB first, otherwise try the supplied {rcpt_host}. This allows you\n"
"# jump over intermediate servers ,like anti-virus appliances, etc.,\n"
"# that would be the immediate next hop.\n"
"#"
;
static const char usage_call_ahead_host[] =
  "Always call-ahead to this host, ignoring call-ahead-db, or the\n"
"# {rcpt_host} macro.\n"
"#"
;
static const char usage_max_failures[] =
  "Maximum number of call-ahead failures initiated from the same\n"
"# client IP before being blocked until the cache entry expires.\n"
"# A value of 0 disables this test.\n"
"#"
;
static const char usage_is_blind_mx[] =
  "Test whether the call-ahead host is blind MX and cache the result so\n"
"# that furture call-aheads to a blind MX can be ignored. A blind MX is\n"
"# a host which accepts any recipient only to bounce later. Some servers\n"
"# like Exchange in their default configuration behave this way. Also\n"
"# catch-all addresses will cause this behaviour too.\n"
"#"
;

static Option optIntro			= { "",				NULL,		"\n# " MILTER_NAME "/" MILTER_VERSION  "\n#\n# " MILTER_COPYRIGHT "\n#\n" };
static Option optBackupMx		= { "backup-mx",		"+",		usage_backup_mx };
static Option optCacheAcceptTTL		= { "cache-accept-ttl",		"604800",	"Cache time-to-live in seconds for positive responses." };
static Option optCacheFile		= { "cache-file",		CACHE_FILE,	"Cache file path for bdb or flatfile types." };
static Option optCacheGcFrequency	= { "cache-gc-frequency", 	"250",		"Cache garbadge collection frequency." };
static Option optCacheRejectTTL		= { "cache-reject-ttl",		"90000",	"Cache time-to-live in seconds for negative responses." };
static Option optCacheType		= { "cache-type",		"bdb",		"Cache type from one of: bdb, flatfile, hash" };
static Option optCallAheadDb		= { "call-ahead-db",		"",		usage_call_ahead_db };
static Option optCallAheadHost		= { "call-ahead-host",		"",		usage_call_ahead_host };
static Option optIgnoreRcptHost		= { "ignore-rcpt-host",		"-",		"Do not call-ahead the {rcpt_host}; see call-ahead-db." };
static Option optIsBlindMx		= { "is-blind-mx",		"-",		usage_is_blind_mx };
static Option optMaxFailures		= { "max-failures",		"0",		usage_max_failures };
static Option optMxLookup		= { "mx-lookup",		"-",		"Perform MX lookup on {rcpt_host} or call-ahead-db table entry." };
static Option optMxReject		= { "mx-reject",		"all",		usage_reserved_ip };
static Option optPrimaryUpReject	= { "primary-up-reject",	"-",		usage_primary_up_reject };
static Option optRelayMailFrom		= { "relay-mail-from",		"-",		"Call-ahead using the original MAIL FROM: instead of the null address." };
static Option optSmtpTimeout		= { "smtp-timeout",		"120",		"SMTP socket timeout used for call-ahead." };

#ifdef ENABLE_TRY_IMPLICIT_MX
static Option optTryImplicitMx		= { "try-implicit-mx",		"-",		"Try the implicit MX for {rcpt_host} if no other MX answers." };
#endif

Option opt_version		= { "version",			NULL,		"Show version and copyright." };

static const char usage_info[] =
  "Write the configuration and compile time options to standard output\n"
"# and exit.\n"
"#"
;
Option opt_info			= { "info", 			NULL,		usage_info };

static Option *optTable[] = {
	&optIntro,
	&optBackupMx,
	&optCacheAcceptTTL,
	&optCacheFile,
	&optCacheGcFrequency,
	&optCacheRejectTTL,
	&optCacheType,
	&optCallAheadDb,
	&optCallAheadHost,
	&optIgnoreRcptHost,
	&opt_info,
	&optIsBlindMx,
	&optMaxFailures,
	&optMxLookup,
	&optMxReject,
	&optPrimaryUpReject,
	&optRelayMailFrom,
	&optSmtpTimeout,
#ifdef ENABLE_TRY_IMPLICIT_MX
	&optTryImplicitMx,
#endif
	&opt_version,
	NULL
};

/***********************************************************************
 *** Stats
 ***********************************************************************/

typedef struct {
	const char *name;
	unsigned long count;
} Stat;

static pthread_mutex_t stat_mutex;

#define STAT_DECLARE(name)	\
static const char stat_name_##name[] = #name; \
static Stat stat_##name = { stat_name_##name }

#define STAT_POINTER(name)	&stat_##name

STAT_DECLARE(start_time);
STAT_DECLARE(run_time);
STAT_DECLARE(connect_active);
STAT_DECLARE(connect_total);
STAT_DECLARE(connect_error);
STAT_DECLARE(transactions);
STAT_DECLARE(access_bl);
STAT_DECLARE(access_wl);
STAT_DECLARE(access_other);
STAT_DECLARE(rcpts_total);
STAT_DECLARE(rcpts_accept);
STAT_DECLARE(rcpts_reject);

#define SMF_MAX_MULTILINE_REPLY		32

static Stat *stat_table[SMF_MAX_MULTILINE_REPLY] = {
	&stat_start_time,
	&stat_run_time,
	&stat_connect_active,
	&stat_connect_total,
	&stat_connect_error,
	&stat_access_bl,
	&stat_access_wl,
	&stat_access_other,
	&stat_transactions,
	&stat_rcpts_total,
	&stat_rcpts_accept,
	&stat_rcpts_reject,
	NULL
};

void
statInit(void)
{
	(void) pthread_mutex_init(&stat_mutex, NULL);
	(void) time((time_t *) &stat_start_time.count);
}

void
statFini(void)
{
	(void) pthreadMutexDestroy(&stat_mutex);
}

void
statGet(Stat *stat, Stat *out)
{
	if (!pthread_mutex_lock(&stat_mutex)) {
		*out = *stat;
		(void) pthread_mutex_unlock(&stat_mutex);
	} else {
		(void) memset(out, 0, sizeof (*out));
	}
}

void
statSetValue(Stat *stat, unsigned long value)
{
	if (!pthread_mutex_lock(&stat_mutex)) {
		stat->count = value;
		(void) pthread_mutex_unlock(&stat_mutex);
	}
}

void
statAddValue(Stat *stat, long value)
{
	if (!pthread_mutex_lock(&stat_mutex)) {
		stat->count += value;
		(void) pthread_mutex_unlock(&stat_mutex);
	}
}

void
statCount(Stat *stat)
{
	statAddValue(stat, 1);
}

/***********************************************************************
 *** Support routines.
 ***********************************************************************/

/*
 * Print a line to the remote SMTP server. Return true
 * on success, otherwise false for a write error.
 */
int
printline(workspace data, char *line)
{
	int rc = 0;

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "> %s", TAG_ARGS, line);

#if defined(NON_BLOCKING_WRITE)
# if ! defined(NON_BLOCKING_READ)
	/* Do not block on sending to the SMTP server just yet. */
	(void) socketSetNonBlocking(data->server, 1);
# endif

	if (socketWrite(data->server, (unsigned char *) line, (long) strlen(line)) == SOCKET_ERROR) {
		syslog(LOG_ERR, TAG_FORMAT "socket write error: %s (%d)", TAG_ARGS, strerror(errno), errno);
		goto error0;
	}

	/* Now wait for the output to be sent to the SMTP server. */
	if (!socketCanSend(data->server, optSmtpTimeout.value)) {
		syslog(LOG_ERR, TAG_FORMAT "timeout before output sent to SMTP server", TAG_ARGS);
		goto error0;
	}
#else
	if (socketWrite(data->server, (unsigned char *) line, (long) strlen(line)) == SOCKET_ERROR) {
		syslog(LOG_ERR, TAG_FORMAT "socket write error: %s (%d)", TAG_ARGS, strerror(errno), errno);
		goto error0;
	}
#endif
	rc = 1;
error0:
#if ! defined(NON_BLOCKING_READ) && defined(NON_BLOCKING_WRITE)
	(void) socketSetNonBlocking(data->server, 0);
#endif
	return rc;
}

int
printlines(workspace data, char **lines)
{
        for ( ; *lines != (char *) 0; lines++) {
        	if (!printline(data, *lines))
        		return 0;
        }

        return 1;
}

int
getSmtpResponse(workspace data, int code, char *line, int linesize, int *status)
{
	char *stop;
	long length, value;

#if defined(NON_BLOCKING_READ) && ! defined(NON_BLOCKING_WRITE)
	/* Do not block on reading from the SMTP server just yet. */
	(void) socketSetNonBlocking(data->server, 1);
#endif

	/* Ideally we should collect _all_ the response lines into a variable
	 * length buffer (see com/snert/lib/util/Buf.h), but I don't see any
	 * real need for it just yet.
	 */

	do {
		/* Reset this return code for each input line of a
		 * multiline response in case there is a read error.
		 */
		value = 450;
		stop = line;

		/* Erase the first 4 bytes of the line buffer, which
		 * corresponds with the 3 ASCII digit status code
		 * followed by either a ASCII hyphen or space.
		 */
		line[0] = line[1] = line[2] = line[4] = '\0';

		switch (length = socketReadLine(data->server, line, linesize)) {
		case SOCKET_ERROR:
			syslog(LOG_ERR, TAG_FORMAT "read error: %s (%d)", TAG_ARGS, strerror(errno), errno);
			goto error0;
		case SOCKET_EOF:
			syslog(LOG_ERR, TAG_FORMAT "unexpected EOF", TAG_ARGS);
			goto error0;
		}

		/* Did we read sufficient characters for a response code? */
		if (length < 4) {
			syslog(LOG_ERR, TAG_FORMAT "truncated response, length=%ld", TAG_ARGS, length);
			goto error0;
		}

		smfLog(SMF_LOG_DIALOG, TAG_FORMAT "< %s", TAG_ARGS, line);

		if ((value = strtol(line, &stop, 10)) == 421) {
			smfLog(SMF_LOG_DIALOG, TAG_FORMAT "SMTP server closing connection", TAG_ARGS);
			break;
		}
	} while (line[3] == '-');
error0:
#if defined(NON_BLOCKING_READ) && ! defined(NON_BLOCKING_WRITE)
	(void) socketSetNonBlocking(data->server, 0);
#endif
	if (status != (int *) 0)
		*status = (int) value;

	return value == code && line + 3 == stop;
}

/***********************************************************************
 *** Cache Functions
 ***********************************************************************/

int
cacheGet(workspace data, char *name, CacheEntry *entry)
{
	int rc;
	Data value;
	struct data key;

	rc = -1;
	*entry = cacheUndefinedEntry;
	DataInitWithBytes(&key, (unsigned char *) name, strlen(name)+1);

	if (pthread_mutex_lock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex lock in cacheGet() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	value = cache->get(cache, &key);

	if (pthread_mutex_unlock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex unlock in cacheGet() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	if (value != NULL) {
		memcpy(entry, value->base(value), value->length(value));
		value->destroy(value);
		rc = 0;
	}

	smfLog(SMF_LOG_CACHE, TAG_FORMAT "cache get key={%s} value={" CACHE_PRINTF_FORMAT "} rc=%d", TAG_ARGS, name, CACHE_PRINTF_ARROW(entry), rc);

	return rc;
}

static int
cacheUpdate(workspace data, char *name, CacheEntry *entry)
{
	int rc;
	Data current;
	CacheEntry old;
	struct data key, value;

	DataInitWithBytes(&key, (unsigned char *) name, strlen(name)+1);

	if (pthread_mutex_lock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex lock in cacheUpdate() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	if ((current = cache->get(cache, &key)) == NULL) {
		old.count = 0;
		old.reply[0] = '\0';
		old.created = time(NULL);
	} else {
		memcpy(&old, current->base(current), current->length(current));
		current->destroy(current);
	}

	entry->count = old.count + 1;
	entry->touched = time(NULL);

	DataInitWithBytes(&value, (unsigned char *) entry, sizeof (*entry) - sizeof (entry->reply) + strlen(entry->reply) + 1);
	rc = cache->put(cache, &key, &value);

	if (pthread_mutex_unlock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex unlock in cacheUpdate() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	smfLog(SMF_LOG_CACHE, TAG_FORMAT "cache update key={%s} value={" CACHE_PRINTF_FORMAT "} rc=%d", TAG_ARGS, name, CACHE_PRINTF_ARROW(entry), rc);

	if (rc)
		syslog(LOG_WARNING, TAG_FORMAT "failed to update cache for <%s>", TAG_ARGS, name);

	return rc;
}

int
cacheExpireEntries(void *key, void *value, void *dataless)
{
	time_t now = time(NULL);
	workspace data = dataless;
	CacheEntry *entry = (CacheEntry *) ((Data) value)->base(value);

	/* Look for start of "accepts any recipient" text, which never expire. */
	if (!isdigit(entry->reply[0]))
		return 1;

	switch (entry->status) {
	case SMFIS_ACCEPT:
	case SMFIS_CONTINUE:
		if (now < entry->touched + optCacheAcceptTTL.value)
			return 1;
		break;

	default:
		if (now < entry->touched + optCacheRejectTTL.value)
			return 1;
		break;
	}

	smfLog(
		SMF_LOG_CACHE, TAG_FORMAT "cache remove key={%s} value={%lx, %ld, %ld} age=%ld",
		TAG_ARGS, ((Data) key)->base(key), entry->touched,
		entry->status, entry->count, now - entry->touched
	);

	return -1;
}


static int
cacheGarbageCollect(workspace data)
{
	unsigned long count = data->work.cid % optCacheGcFrequency.value;

	smfLog(SMF_LOG_CACHE, TAG_FORMAT "%lu connections", TAG_ARGS, count);

	if (count == 1) {
		if (pthread_mutex_lock(&smfMutex))
			syslog(LOG_ERR, TAG_FORMAT "mutex lock in cacheGarbageCollect() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

		smfLog(SMF_LOG_CACHE, TAG_FORMAT "garbage collecting cache", TAG_ARGS);

		cache->walk(cache, cacheExpireEntries, data);

		smfLog(SMF_LOG_CACHE, TAG_FORMAT "syncing cache", TAG_ARGS);

		if (cache->sync(cache))
			syslog(LOG_ERR, TAG_FORMAT "cache sync error: %s (%d)", TAG_ARGS, strerror(errno), errno);

		if (pthread_mutex_unlock(&smfMutex))
			syslog(LOG_ERR, TAG_FORMAT "mutex unlock in cacheGarbageCollect() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);
	}

	return 0;
}

/***********************************************************************
 *** Handlers
 ***********************************************************************/

/*
 * Open and allocate per-connection resources.
 */
static sfsistat
filterOpen(SMFICTX *ctx, char *client_name, _SOCK_ADDR *raw_client_addr)
{
	int access;
	workspace data;

	if (raw_client_addr == NULL) {
		smfLog(SMF_LOG_TRACE, "filterOpen() got NULL socket address, accepting connection");
		goto error0;
	}

	if (raw_client_addr->sa_family != AF_INET
#ifdef HAVE_STRUCT_SOCKADDR_IN6
	&& raw_client_addr->sa_family != AF_INET6
#endif
	) {
		smfLog(SMF_LOG_TRACE, "filterOpen() unsupported socket address type, accepting connection");
		goto error0;
	}

	if ((data = calloc(1, sizeof *data)) == NULL)
		goto error0;

	smfProlog(&data->work, ctx, client_name, raw_client_addr);
	data->work.info = &milter;

	smfLog(SMF_LOG_TRACE, TAG_FORMAT "filterOpen(%lx, '%s', [%s])", TAG_ARGS, (long) ctx, data->work.client_name, data->work.client_addr);

	if (smfi_setpriv(ctx, (void *) data) == MI_FAILURE) {
		syslog(LOG_ERR, TAG_FORMAT "failed to save workspace", TAG_ARGS);
		goto error1;
	}

	access = smfAccessHost(&data->work, MILTER_NAME "-connect:", data->work.client_name, data->work.client_addr, SMDB_ACCESS_OK);

	switch (access) {
	case SMDB_ACCESS_REJECT:
		/* Report this mail error ourselves, because sendmail/milter API
		 * fails to report xxfi_connect handler rejections.
		 */
		statCount(&stat_access_bl);
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "connection %s [%s] blocked", TAG_ARGS, client_name, data->work.client_addr);
		return smfReply(&data->work, 550, "5.7.1", "connection %s [%s] blocked", client_name, data->work.client_addr);

	case SMDB_ACCESS_ERROR:
		statCount(&stat_access_other);
		return SMFIS_REJECT;

	case SMDB_ACCESS_OK:
		statCount(&stat_access_wl);
		statAddValue(&stat_connect_active, 1);
		smfLog(SMF_LOG_TRACE, TAG_FORMAT "client %s [%s] white listed", TAG_ARGS, client_name, data->work.client_addr);
		data->work.skipConnection = 1;

		/* Don't use SMFIS_ACCEPT, otherwise we can't do STAT
		 * from localhost.
		 */
		return SMFIS_CONTINUE;
	}

	statAddValue(&stat_connect_active, 1);

	return SMFIS_CONTINUE;
error1:
	free(data);
error0:
	statCount(&stat_connect_error);

	return SMFIS_ACCEPT;
}

static sfsistat
filterMail(SMFICTX *ctx, char **args)
{
	int access;
	workspace data;
	char *auth_authen;

	if ((data = (workspace) smfi_getpriv(ctx)) == NULL)
		return smfNullWorkspaceError("filterMail");

	if ((data->work.qid = smfi_getsymval(ctx, "i")) == NULL)
		data->work.qid = smfNoQueue;

	free(data->work.mail);
	data->work.mail = NULL;
	data->work.skipMessage = data->work.skipConnection;

	smfLog(SMF_LOG_TRACE, TAG_FORMAT "filterMail(%lx, %lx) MAIL='%s'", TAG_ARGS, (long) ctx, (long) args, args[0]);

	access = smfAccessMail(&data->work, MILTER_NAME "-from:", args[0], SMDB_ACCESS_UNKNOWN);

	switch (access) {
	case SMDB_ACCESS_REJECT:
		statCount(&stat_access_bl);
		return smfReply(&data->work, 550, "5.7.1", "sender blocked");

	case SMDB_ACCESS_OK:
		statCount(&stat_access_wl);
		smfLog(SMF_LOG_TRACE, TAG_FORMAT "sender %s white listed", TAG_ARGS, args[0]);
		data->work.skipMessage = 1;
		return SMFIS_ACCEPT;

	/* smfAccessMail failure cases. */
	case SMDB_ACCESS_TEMPFAIL:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "sender %s temp.failed", TAG_ARGS, args[0]);
		statCount(&stat_access_other);
		return SMFIS_TEMPFAIL;

	case SMDB_ACCESS_ERROR:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "sender %s unknown error", TAG_ARGS, args[0]);
		statCount(&stat_access_other);
		return SMFIS_REJECT;
	}

	auth_authen = smfi_getsymval(ctx, "{auth_authen}");
	access = smfAccessAuth(&data->work, MILTER_NAME "-auth:", auth_authen, args[0], NULL, NULL);

	switch (access) {
	case SMDB_ACCESS_REJECT:
		statCount(&stat_access_bl);
		return smfReply(&data->work, 550, "5.7.1", "sender blocked");

	case SMDB_ACCESS_OK:
		statCount(&stat_access_wl);
		smfLog(SMF_LOG_TRACE, TAG_FORMAT "authenticated id <%s> white listed", TAG_ARGS, auth_authen);
		data->work.skipMessage = 1;
		return SMFIS_ACCEPT;

	/* smfAccessAuth failure cases. */
	case SMDB_ACCESS_TEMPFAIL:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "authenticated id <%s> temp.failed", TAG_ARGS, auth_authen);
		statCount(&stat_access_other);
		return SMFIS_TEMPFAIL;

	case SMDB_ACCESS_ERROR:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "authenticated id <%s> unknown error", TAG_ARGS, auth_authen);
		statCount(&stat_access_other);
		return SMFIS_REJECT;
	}

	statCount(&stat_transactions);

	return SMFIS_CONTINUE;
}

static int
mxConnect(workspace data, char *domain)
{
	PDQ_MX *mx;
	PDQ_rr *list;
	Socket2 *socket;
	int rc, preference;

	rc = -1;
	data->server = NULL;

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "mxConnect(%lx, '%s')", TAG_ARGS, (long) data, domain);

	/* Make sure the domain is not bound by square bracket, which
	 * disable MX lookups.
	 */
	if (*domain == '[') {
		smfLog(SMF_LOG_DIALOG, TAG_FORMAT "%s: square brackets disables MX lookup", TAG_ARGS, domain);
		goto error0;
	}

	if ((list = pdqFetch(PDQ_CLASS_IN, PDQ_TYPE_MX, domain, NULL)) == NULL) {
		syslog(LOG_ERR, TAG_FORMAT "%s: MX lookup error: %s (%d)", TAG_ARGS, domain, strerror(errno), errno);
		goto error0;
	}

	/* Did we get a result we can use and is it a valid domain? */
 	if (((PDQ_QUERY *)list)->rcode != PDQ_RCODE_OK) {
		syslog(LOG_ERR, TAG_FORMAT "%s: error %s", TAG_ARGS, domain, pdqRcodeName(((PDQ_QUERY *)list)->rcode));
		goto error1;
	}

	if (smfLogDetail & SMF_LOG_DIALOG)
		pdqListLog(list);

	list = pdqListPrune(list, IS_IP_TEST_NET|IS_IP_LOCAL|IS_IP_LINK_LOCAL|IS_IP_MULTICAST|IS_IP_V6_RESERVED);

	if (list == NULL) {
		syslog(LOG_ERR, TAG_FORMAT "%s: has no acceptable MX", TAG_ARGS, domain);
		goto error0;
	}

	/* Find preference weight of connected client. */
	preference = 65535;
	if ((mx = (PDQ_MX *) pdqListFindHost(list, PDQ_CLASS_IN, PDQ_TYPE_MX, data->work.client_name)) != NULL)
		preference = mx->preference;

	/* Do not ignore the implicit MX record. */
	if (preference == 0)
		preference = 65535;

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "MX preference < %d", TAG_ARGS, preference);

	/* Try all MX of a lower preference until one answers. */
	socket = NULL;
	for (mx = (PDQ_MX *) list; mx != NULL; mx = (PDQ_MX *) mx->rr.next) {
		if (mx->rr.section == PDQ_SECTION_QUERY
		|| mx->rr.type != PDQ_TYPE_MX || preference <= mx->preference)
			continue;

		if ((socket = socketConnect(mx->host.string.value, SMTP_PORT, optSmtpTimeout.value)) != NULL) {
			smfLog(SMF_LOG_DIALOG, TAG_FORMAT "connected to MX %d %s", TAG_ARGS, mx->preference, mx->host.string.value);

			fileSetCloseOnExec(socketGetFd(socket), 1);
			socketFdSetKeepAlive(socketGetFd(socket), 1, SMTP_COMMAND_TO, 60, 3);
			socketSetTimeout(socket, optSmtpTimeout.value);
			(void) socketSetNonBlocking(socket, 1);
			rc = 0;
			break;
		}
	}

#ifdef ENABLE_TRY_IMPLICIT_MX
	if (rc == -1
	&& optTryImplicitMx.value
	&& (socket = socketConnect(domain, SMTP_PORT, optSmtpTimeout.value)) == NULL) {
		smfLog(SMF_LOG_DIALOG, TAG_FORMAT "connected to MX 0 %s", TAG_ARGS, domain);
		rc = 0;
	}
#endif
	data->server = socket;
error1:
	pdqFree(list);
error0:
	return rc;
}

static sfsistat
filterRcpt(SMFICTX *ctx, char **args)
{
	sfsistat rc;
	workspace data;
	CacheEntry entry;
	int status, access;
	char *auth_authen, *rcpt_addr, *rcpt_host, *rcpt_mailer, *helo, *value;

	value = NULL;
	rc = SMFIS_CONTINUE;

	if ((data = (workspace) smfi_getpriv(ctx)) == NULL)
		return smfNullWorkspaceError("filterRcpt");

	free(data->work.rcpt);
	data->work.rcpt = NULL;
	statCount(&stat_rcpts_total);

	if ((rcpt_addr = smfi_getsymval(ctx, "{rcpt_addr}")) == NULL || *rcpt_addr == '\0')
		rcpt_addr = args[0];

	/* NOTE that Postfix does not support {rcpt_host} or {rcpt_mailer}. */
	if ((rcpt_host = smfi_getsymval(ctx, "{rcpt_host}")) == NULL || *rcpt_host == '\0')
		rcpt_host = (char *) smfUndefined;

	if ((rcpt_mailer = smfi_getsymval(ctx, "{rcpt_mailer}")) == NULL || *rcpt_mailer == '\0')
		rcpt_mailer = (char *) smfUndefined;

	auth_authen = smfi_getsymval(ctx, "{auth_authen}");

	smfLog(
		SMF_LOG_TRACE,
		TAG_FORMAT "filterRcpt(%lx, %lx) RCPT='%s' rcpt_addr='%s' rcpt_host='%s' rcpt_mailer='%s'",
		TAG_ARGS, (long) ctx, (long) args, args[0], rcpt_addr, rcpt_host, rcpt_mailer
	);

	/* BY-PASS if the sender is authenticated. */
	if (auth_authen != NULL) {
		smfLog(SMF_LOG_INFO, TAG_FORMAT "authenticated sender \"%s\", skipping", TAG_ARGS, auth_authen);
		goto error0;
	}

	access = smfAccessRcpt(&data->work, MILTER_NAME "-to:", args[0]);

	switch (access) {
	case SMDB_ACCESS_REJECT:
		statCount(&stat_access_bl);
		return smfReply(&data->work, 550, "5.7.1", "recipient blocked");

	case SMDB_ACCESS_OK:
		statCount(&stat_access_wl);
		smfLog(SMF_LOG_TRACE, TAG_FORMAT "recipient %s white listed", TAG_ARGS, args[0]);
		data->work.skipMessage = 1;
		return SMFIS_ACCEPT;

	/* smfAccessRcpt failure cases. */
	case SMDB_ACCESS_TEMPFAIL:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "recipient %s temp.failed", TAG_ARGS, args[0]);
		statCount(&stat_access_other);
		return SMFIS_TEMPFAIL;

	case SMDB_ACCESS_ERROR:
		smfLog(SMF_LOG_ERROR, TAG_FORMAT "recipient %s unknown error", TAG_ARGS, args[0]);
		statCount(&stat_access_other);
		return SMFIS_REJECT;
	}

	if (rcpt_addr == args[0])
		rcpt_addr = data->work.rcpt->address.string;

	/* BY-PASS if the MX needs to be looked up. */
	if (*optCallAheadHost.string == '\0') {
		/* call-ahead-db values are similar to mailertable, thus smdbAccess
		 * routinues should always return SMDB_ACCESS_UNKNOWN and a string;
		 * anything else is invalid for call-ahead-db and can be ignored.
		 */
		if (smdbAccessDomain(callAheadDb, NULL, data->work.rcpt->domain.string, NULL, &value) == SMDB_ACCESS_UNKNOWN) {
			char *mailer;

			/* We now support the use of a mailertable formatted
			 * file where the right-hand-side can be prefixed with
			 * mailer:. As such we have to support the error: mailer
			 * as an indication that we won't route for this domain.
			 */
			if (0 <= TextInsensitiveStartsWith(value, "error:")) {
				smfLog(SMF_LOG_INFO, TAG_FORMAT "call-ahead-db domain=%s %s, rejecting", TAG_ARGS, data->work.rcpt->domain.string, value);
				rc = SMFIS_REJECT;
				goto error0;
			}

			/* In sendmail, the local: mailer specifies a local
			 * user name in place of a domain name. So we skip the
			 * call-ahead and let sendmail deal with local delivery
			 * and report user unknown if necessary.
			 */
			if (0 <= TextInsensitiveStartsWith(value, "local:")) {
				smfLog(SMF_LOG_INFO, TAG_FORMAT "call-ahead-db domain=%s %s, skipping", TAG_ARGS, data->work.rcpt->domain.string, value);
				goto error0;
			}

			rcpt_host = value;

			/* Skip optional leading mailer: name in value string.
			 * This allows sendmail or postfix mailertables to be
			 * used without modification.
			 *
			 *	esmtp:[192.0.2.7]
			 *	smtp:snert.net
			 *	some-mailer:[mx.snert.net]
			 *	relay:[2001:0DB8::DEAD:BEEF]:8025
			 */
			for (mailer = value; *mailer != '\0'; ++mailer) {
				if (isalnum(*mailer) || *mailer == '-' || *mailer == '_')
					continue;
				if (*mailer == ':') {
					rcpt_host = mailer+1;
					break;
				}
			}

			smfLog(SMF_LOG_DEBUG, TAG_FORMAT "call-ahead-db domain=%s sets rcpt_host=%s", TAG_ARGS, data->work.rcpt->domain.string, rcpt_host);
		} else if (optIgnoreRcptHost.value) {
			smfLog(SMF_LOG_DEBUG, TAG_FORMAT "no next hop in table, skipping", TAG_ARGS);
			goto error0;
		}

		if (!optMxLookup.value && *rcpt_host != '[') {
			smfLog(SMF_LOG_INFO, TAG_FORMAT "rcpt_host='%s' is not a defined route, skipping", TAG_ARGS, rcpt_host);
			goto error0;
		}
	} else {
		rcpt_host = optCallAheadHost.string;
		smfLog(SMF_LOG_DEBUG, TAG_FORMAT "call-ahead-host sets rcpt_host=%s", TAG_ARGS, rcpt_host);
	}

	if (rcpt_host == smfUndefined || *rcpt_host == '\0') {
		smfLog(SMF_LOG_INFO, TAG_FORMAT "local recipient, skipping", TAG_ARGS);
		goto error0;
	}

	if (0 < optMaxFailures.value && !data->work.skipMessage && cacheGet(data, data->work.client_addr, &entry) == 0 && optMaxFailures.value <= entry.count) {
		rc = mfReply(ctx, "550", "5.7.1", "too many failures %lu from %s [%s]",  entry.count, data->work.client_name, data->work.client_addr);
		goto error0;
	}

	smfLog(SMF_LOG_DEBUG, TAG_FORMAT "failures %lu from %s [%s]", TAG_ARGS, entry.count, data->work.client_name, data->work.client_addr);

	/* Check for accept-the-bounce domains / hosts. */
	if (optIsBlindMx.value && *rcpt_host != '\0' && cacheGet(data, rcpt_host, &entry) == 0) {
		smfLog(SMF_LOG_INFO, TAG_FORMAT "" HOP_INFO_FORMAT "accepts any recipient, skipping", TAG_ARGS, HOP_INFO_ARGS);
		goto error0;
	}

	if (cacheGet(data, rcpt_addr, &entry) == 0) {
		/* BY-PASS if the recipient address is known. The cache entry
		 * is not touched and allowed to expire.
		 *
		 * NOTE the TEMPFAIL case is not acted on. Its better to perfom
		 * the call-ahead again in case the previous temporary error state
		 * has been resolved, ie. consider mailbox full, high system load,
		 * temporary DNS errors, etc. that can cause temp. fail. Caching
		 * those case is not ideal, since the cache entry might live longer
		 * than the temp. fail condition unnecessary causing mail delay.
		 */
		switch (entry.status) {
		case SMFIS_ACCEPT:
		case SMFIS_CONTINUE:
			if (time(NULL) < entry.touched + optCacheAcceptTTL.value) {
				smfLog(SMF_LOG_INFO, TAG_FORMAT "recipient <%s> (%d) cached, skipping", TAG_ARGS, rcpt_addr, entry.status);
				goto error0;
			}
			break;

		case SMFIS_REJECT:
			if (time(NULL) < entry.touched + optCacheRejectTTL.value) {
				rc = mfReply(ctx, "550", NULL, HOP_INFO_FORMAT "previously cached response: \"%s\"", HOP_INFO_ARGS, entry.reply);

				/* Update the cache for the client address
				 * based on this call-ahead cache hit.
				 */
				(void) cacheUpdate(data, data->work.client_addr, &entry);
				goto error0;
			}
			break;
		}
	}

	smfLog(
		SMF_LOG_PARSE,
		TAG_FORMAT "address='%s' localleft='%s' localright='%s' domain='%s'",
		TAG_ARGS, data->work.rcpt->address.string, data->work.rcpt->localLeft.string,
		data->work.rcpt->localRight.string, data->work.rcpt->domain.string
	);

	if (*data->work.rcpt->address.string == '\0') {
		rc = mfReply(ctx, "553", "5.1.0", "cannot deliver to null address");
		goto error0;
	}

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "contacting " HOP_INFO_FORMAT, TAG_ARGS, HOP_INFO_ARGS);

	/* Connect to next hop. */
	data->server = NULL;
	if (*optCallAheadHost.string != '\0') {
		smfLog(SMF_LOG_DIALOG, TAG_FORMAT "trying to connect to host %s...", TAG_ARGS, rcpt_host);
		if (socketOpenClient(rcpt_host, SMTP_PORT, optSmtpTimeout.value, NULL, &data->server) == 0)
			smfLog(SMF_LOG_DIALOG, TAG_FORMAT "connected to host %s", TAG_ARGS, rcpt_host);
	} else if (!optMxLookup.value || (mxConnect(data, rcpt_host) && !optIgnoreRcptHost.value)) {
		smfLog(SMF_LOG_DIALOG, TAG_FORMAT "trying to connect to host %s...", TAG_ARGS, rcpt_host);
		if ((data->server = socketConnect(rcpt_host, SMTP_PORT, optSmtpTimeout.value)) == NULL)
			smfLog(SMF_LOG_DIALOG, TAG_FORMAT "connected to host %s", TAG_ARGS, rcpt_host);
	}

	if (data->server == NULL) {
 		if (rcpt_host == smfUndefined) {
			smfLog(SMF_LOG_INFO, TAG_FORMAT "looks like a local recipient, skipping", TAG_ARGS);
			rc = SMFIS_CONTINUE;
		}

		else if (optBackupMx.value)
			rc = SMFIS_CONTINUE;
		else
			rc = mfReply(ctx, "450", "4.7.1", HOP_INFO_FORMAT "not answering ", HOP_INFO_ARGS);
		goto error0;
	}

	socketSetTimeout(data->server, optSmtpTimeout.value);

#if defined(NON_BLOCKING_READ) && defined(NON_BLOCKING_WRITE)
	/* Set non-blocking I/O once for both getSmtpResponse() and
	 * printline() and leave it that way.
	 */
	if (socketSetNonBlocking(data->server, 1)) {
		syslog(LOG_ERR, TAG_FORMAT "internal error: socketSetNonBlocking() failed: %s (%d)", TAG_ARGS, strerror(errno), errno);
		rc = mfReply(ctx, "451", "4.4.3", HOP_INFO_FORMAT "communication error", HOP_INFO_ARGS);
		goto error1;
	}
#endif
	/* Read welcome response. */
	if (!getSmtpResponse(data, 220, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
		if (optBackupMx.value && (status == 421 || status == 554)) {
			rc = SMFIS_CONTINUE;
			goto error1;
		}

		switch (status) {
		case 421:
			rc = mfReply(ctx, "421", NULL, HOP_INFO_FORMAT "responded with a busy signal", HOP_INFO_ARGS);
			goto error2;
		case 554:
			rc = mfReply(ctx, "554", NULL, HOP_INFO_FORMAT "provides no SMTP service", HOP_INFO_ARGS);
			goto error2;
		default:
			rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "responded with \"%s\"", status, status / 100, HOP_INFO_ARGS, data->line);
			goto error2;
		}
	}

	/* The next hop is alive and willing to receive. */
	if (optPrimaryUpReject.value && !isReservedIP(data->work.client_addr, IS_IP_LOCAL|IS_IP_LAN) && *optCallAheadHost.string == '\0') {
		/* This does not conform with RFC 974 section "Interpreting
		 * the List of MX RRs", paragraph 7, sentence 2 and 3, which
		 * only requires mail clients to attempt delivery to the
		 * primary first, before trying other MXes. This option
		 * essentially demands that a client only deliver to the
		 * primary MX when its available.
		 */
		rc = mfReply(ctx, "450", "4.7.1", "primary MX %s online and accepting mail", rcpt_host);

		/* Don't cache this result. */
		goto error1;
	}

	/* TEST: Send our hello. Failure to accept us indicates an
	 * unwillingness to accept any mail from us. Return the
	 * favour.
	 */
	status = 450;

	if ((helo = smfi_getsymval(ctx, smMacro_if_name)) == NULL
	&&  (helo = smfi_getsymval(ctx, smMacro_if_addr)) == NULL
	&&  (helo = smfi_getsymval(ctx, "j")) == NULL)
		helo = smfOptInterfaceName.string;

	(void) snprintf(data->line, sizeof (data->line), "HELO %s\r\n", helo);
	if (!printline(data, data->line)
	|| !getSmtpResponse(data, 250, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
		rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "did not accept HELO", status, status / 100,  HOP_INFO_ARGS);
		goto error2;
	}

	/* TEST: Use the DSN address to verify that they're playing
	 * by the rules. Also using the DSN address avoids loops
	 * in the case of both systems using milter-sender.
	 */
	status = 450;
	(void) snprintf(data->line, sizeof (data->line), "MAIL FROM:<%s>\r\n", optRelayMailFrom.value && data->work.mail != NULL ? data->work.mail->address.string : "");
	if (!printline(data, data->line)
	|| !getSmtpResponse(data, 250, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
		if (optRelayMailFrom.value)
			rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "rejected sender address saying \"%s\"", status, status / 100,  HOP_INFO_ARGS);
		else
			rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "does not accept <> address as required by RFC 821, 1123, 2505, and 2821", status, status / 100,  HOP_INFO_ARGS);
		goto error2;
	}

	/* TEST: Finally see if they're willing to accept email for
	 * the recipient. An error here probably means an user unknown,
	 * mailbox full, or similar nonsense, in which case we don't
	 * want to deal with them.
	 */
	(void) snprintf(data->line, SMTP_TEXT_LINE_LENGTH, "RCPT TO:<%s>\r\n", rcpt_addr);

	status = 450;
	if (!printline(data, data->line)
	|| !getSmtpResponse(data, 250, entry.reply, sizeof (entry.reply), &status)) {
		/* Skip leading status and extended status codes */
		int len = strspn(entry.reply, "0123456789. -");
		rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "rejected address saying \"%s\"", status, status / 100,  HOP_INFO_ARGS, entry.reply + len);
		goto error2;
	}

	if (optIsBlindMx.value) {
		status = 450;
		if (!printline(data, "RSET\r\n")
		|| !getSmtpResponse(data, 250, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
			/* Skip leading status and extended status codes */
			rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "did not accept RSET", status, status / 100,  HOP_INFO_ARGS);
			goto error2;
		}

		status = 450;
		(void) snprintf(data->line, sizeof (data->line), "MAIL FROM:<%s>\r\n", optRelayMailFrom.value && data->work.mail != NULL ? data->work.mail->address.string : "");
		if (!printline(data, data->line)
		|| !getSmtpResponse(data, 250, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
			if (optRelayMailFrom.value)
				rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "rejected sender address saying \"%s\"", status, status / 100,  HOP_INFO_ARGS);
			else
				rc = mfReply(ctx, NULL, NULL, "%d %d.7.1 " HOP_INFO_FORMAT "does not accept <> address as required by RFC 821, 1123, 2505, and 2821", status, status / 100,  HOP_INFO_ARGS);
			goto error2;
		}

		/* Generate a false address. */
		(void) snprintf(
			data->line, SMTP_TEXT_LINE_LENGTH, "RCPT TO:<%s%c@%s>\r\n",
			data->work.rcpt->localLeft.string, LuhnGenerate(rcpt_addr)+'0',
			data->work.rcpt->domain.string
		);
		TextReverse(data->line + 9, data->work.rcpt->localLeft.length);
		TextInvert(data->line + 9, data->work.rcpt->localLeft.length);

		status = 450;
		(void) printline(data, data->line);
		if (getSmtpResponse(data, 250, data->line, SMTP_TEXT_LINE_LENGTH, &status)) {
			smfLog(SMF_LOG_DIALOG, TAG_FORMAT "" HOP_INFO_FORMAT "accepts any recipient", TAG_ARGS, HOP_INFO_ARGS);
			TextCopy(entry.reply, sizeof (entry.reply), "accepts any recipient");
			(void) cacheUpdate(data, rcpt_host, &entry);
			rc = SMFIS_CONTINUE;
			goto error1;
		}
	}

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "" HOP_INFO_FORMAT "accepted recipient", TAG_ARGS, HOP_INFO_ARGS);

	rc = SMFIS_CONTINUE;
error2:
	/* Cache the result of the call ahead (success or failure).
	 *
	 * We can survive without the cache, though performance may
	 * degrade, since we will retest each message to this recipient.
	 */
	entry.status = rc;
	(void) cacheUpdate(data, rcpt_addr, &entry);

	/* Do not cache temporary failure results. */
	if (rc != SMFIS_TEMPFAIL) {
		(void) cacheUpdate(data, data->work.client_addr, &entry);
	}
error1:
	/* Some how we are getting ENOTSOCK during getSmtpResponse(),
	 * probably from a dropped connection or some such. However
	 * attempting then to send the QUIT appears to crash the
	 * milter. So now if there is any sort of error, we drop
	 * the connection hard, instead of politely.
	 */
	if (errno == 0 && printline(data, "QUIT\r\n")) {
#ifdef ORIGINALLY
		/* Don't wait to read a response from the QUIT,
		 * since some SMTP servers drop the connection
		 * without sending the response.
		 */
#else
		/* Wait only a short time for the response to
		 * QUIT, since some SMTP servers choose to drop
		 * the connection without sending a response.
		 */
		socketSetTimeout(data->server, SOCKET_TIMEOUT_QUIT);
		(void) getSmtpResponse(data, 221, data->line, SMTP_TEXT_LINE_LENGTH, &status);
#endif
	}

	smfLog(SMF_LOG_DIALOG, TAG_FORMAT "closing SMTP connection", TAG_ARGS);
	socketClose(data->server);
	data->server = NULL;
error0:
	statCount((rc == SMFIS_REJECT || rc == SMFIS_TEMPFAIL) ? &stat_rcpts_reject : &stat_rcpts_accept);
	free(value);

	return rc;
}

#if SMFI_VERSION > 2
static int
cacheRemove(workspace data, char *name)
{
	int rc;
	struct data key;

	if (pthread_mutex_lock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex lock in cacheRemove() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	if (name == NULL) {
		rc = cache->removeAll(cache);
	} else {
		DataInitWithBytes(&key, (unsigned char *) name, strlen(name)+1);
		rc = cache->remove(cache, &key);
	}

	if (pthread_mutex_unlock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex unlock in cacheRemove() failed: %s (%d) ", TAG_ARGS, strerror(errno), errno);

	smfLog(SMF_LOG_CACHE, TAG_FORMAT "cache remove key={%s} rc=%d", TAG_ARGS, name == NULL ? "(ALL)" : name, rc);

	return rc;
}

static sfsistat
statCommand(SMFICTX * ctx, const char *command)
{
	sfsistat rc;
	Stat **stat;
	Vector words;
	workspace data;
	char stamp[40];
	struct tm local;
	unsigned long age, d, h, m, s;
	size_t buffer_length, line_length;
	char buffer[2048], *lines[SMF_MAX_MULTILINE_REPLY], **line;

	rc = SMFIS_CONTINUE;

	if ((data = (workspace) smfi_getpriv(ctx)) == NULL)
		return smfNullWorkspaceError("statCommand");

	smfLog(SMF_LOG_TRACE, TAG_FORMAT "statCommand(%lx, '%s')", TAG_ARGS, (long) ctx, command);

	if ((words = TextSplit(command, " \t", 0)) == NULL)
		goto error0;
	if (VectorLength(words) != 2)
		goto error1;
	if (TextInsensitiveCompare("STAT", VectorGet(words, 0)) != 0)
		goto error1;
	if (TextInsensitiveCompare(MILTER_NAME, VectorGet(words, 1)) != 0)
		goto error1;

	/* Only localhost can query the status for security. */
	if (!isReservedIP(data->work.client_addr, IS_IP_LOOPBACK|IS_IP_LOCALHOST)) {
		rc = SMFIS_REJECT;
		goto error1;
	}

	line = lines;
	buffer_length = 0;

	(void) localtime_r((time_t *) &stat_start_time.count, &local);
	(void) strftime(stamp, sizeof (stamp), "%a, %d %b %Y %H:%M:%S %z", &local);
	line_length = snprintf(buffer+buffer_length, sizeof (buffer)-buffer_length, "%s=%s", stat_start_time.name, stamp);
	*line++ = buffer + buffer_length;
	buffer_length += line_length+1;

	age = s = (unsigned long) (time(NULL) - (time_t) stat_start_time.count);
	d = s / 86400;
	s -= d * 86400;
	h = s / 3600;
	s -= h * 3600;
	m = s / 60;
	s -= m * 60;

	line_length = snprintf(buffer+buffer_length, sizeof (buffer)-buffer_length, "%s=%lu (%.2lu %.2lu:%.2lu:%.2lu)", stat_run_time.name, age, d, h, m, s);
	*line++ = buffer + buffer_length;
	buffer_length += line_length+1;

	for (stat = stat_table+2; *stat != NULL; stat++) {
		line_length = snprintf(buffer+buffer_length, sizeof (buffer)-buffer_length, "%s=%lu", (*stat)->name, (*stat)->count);
		*line++ = buffer + buffer_length;
		buffer_length += line_length+1;
	}
	*line = NULL;

	(void) smfMultiLineReplyA(&data->work, 411, "4.0.0", lines);
	rc = SMFIS_TEMPFAIL;
error1:
	VectorDestroy(words);
error0:
	return rc;
}

static sfsistat
filterUnknown(SMFICTX * ctx, const char *command)
{
	char *word;
	sfsistat rc;
	Vector words;
	workspace data;
	CacheEntry entry;

	rc = SMFIS_CONTINUE;

	if ((data = (workspace) smfi_getpriv(ctx)) == NULL)
		return smfNullWorkspaceError("filterUnknown");

	smfLog(SMF_LOG_TRACE, TAG_FORMAT "filterUnknown(%lx, '%s')", TAG_ARGS, (long) ctx, command);

	if ((rc = statCommand(ctx, command)) != SMFIS_CONTINUE)
		goto error0;

	/* Only accept this command from permitted hosts. */
#ifdef RESTRICT_COMMANDS_TO_LOCALHOST
	if (!isReservedIP(data->work.client_addr, IS_IP_LOOPBACK|IS_IP_LOCALHOST))
#else
	if (smfAccessClient(&data->work, MILTER_NAME "-command:", data->work.client_name, data->work.client_addr, NULL, NULL) != SMDB_ACCESS_OK)
#endif
		goto error0;

	if ((words = TextSplit(command, " \t", 0)) == NULL)
		goto error0;

	if ((word = VectorGet(words, 0)) == NULL)
		goto error1;

	if (strcmp(word, MILTER_NAME) != 0)
		goto error1;

	if ((word = VectorGet(words, 1)) == NULL)
		goto error1;

	/***
	 *** Responses to unknown command are only returned once an SMTP
	 *** transaction has been started, ie. a valid MAIL FROM: given.
	 *** Commands issued before HELO or before MAIL FROM: result in
	 *** the command being processed and the connection being dropped
	 *** without returning a positive or negative response. Also there
	 *** is no way to return a 2xx response with a reply.
	 ***/

	if (strcmp(word, "cache-remove") == 0) {
		if ((word = VectorGet(words, 2)) == NULL) {
			rc = smfReply(&data->work, 500, "5.5.4", "invalid argument");
			goto error1;
		}

		if (cacheRemove(data, word))
			rc = smfReply(&data->work, 500, "5.5.0", "not found");
		else
			rc = smfReply(&data->work, 500, "5.0.0", "removed");
	} else if (strcmp(word, "cache-remove-all") == 0) {
		if (cacheRemove(data, NULL))
			rc = smfReply(&data->work, 500, "5.5.0", "not found");
		else
			rc = smfReply(&data->work, 500, "5.0.0", "removed");
	} else if (strcmp(word, "cache-get") == 0) {
		if ((word = VectorGet(words, 2)) == NULL) {
			rc = smfReply(&data->work, 500, "5.5.4", "invalid argument");
			goto error1;
		}

		if (cacheGet(data, word, &entry))
			rc = smfReply(&data->work, 500, "5.5.0", "not found");
		else
			rc = smfReply(&data->work, 500, "5.0.0", "key={%s} value={%lx %ld %ld}", word, entry.touched, entry.status, entry.count);
	}
error1:
	VectorDestroy(words);
error0:
	return rc;
}
#endif

/*
 * Close and release per-connection resources.
 */
static sfsistat
filterClose(SMFICTX *ctx)
{
	workspace data;
	unsigned short cid = 0;

	if ((data = (workspace) smfi_getpriv(ctx)) != NULL) {
		cid = smfCloseEpilog(&data->work);
		cacheGarbageCollect(data);
		free(data);
	}

	smfLog(SMF_LOG_TRACE, TAG_FORMAT "filterClose(%lx)", cid, smfNoQueue, (long) ctx);

	statAddValue(&stat_connect_active, -1);

	return SMFIS_CONTINUE;
}

/***********************************************************************
 ***  Milter Definition Block
 ***********************************************************************/

static smfInfo milter = {
	MILTER_MAJOR,
	MILTER_MINOR,
	MILTER_BUILD,
	MILTER_NAME,
	MILTER_VERSION,
	MILTER_COPYRIGHT,
	RUN_AS_USER,
	RUN_AS_GROUP,
	MILTER_CF,
	PID_FILE,
	"unix:" SOCKET_FILE,
	WORK_DIR,
	SMF_STDIO_CLOSE,

	/* struct smfiDesc block */
	{
		MILTER_NAME,		/* filter name */
		SMFI_VERSION,		/* version code -- do not change */
		0,			/* flags */
		filterOpen,		/* connection info filter */
		NULL,			/* SMTP HELO command filter */
		filterMail,		/* envelope sender filter */
		filterRcpt,		/* envelope recipient filter */
		NULL,			/* header filter */
		NULL,			/* end of header */
		NULL,			/* body block filter */
		NULL,			/* end of message */
		NULL,			/* message aborted */
		filterClose		/* connection cleanup */
#if SMFI_VERSION > 2
		, filterUnknown		/* Unknown/unimplemented commands */
#endif
#if SMFI_VERSION > 3
		, NULL			/* SMTP DATA command */
#endif
#if SMFI_VERSION >= 0x01000000
		, NULL			/* xxfi_negotiate */
#endif
	}
};

/***********************************************************************
 *** Startup
 ***********************************************************************/

static void
atExitCleanUp()
{
	if (pthread_mutex_lock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex lock in atExitCleanUp() failed: %s (%d) ", 0, smfNoQueue, strerror(errno), errno);

	if (cache != NULL) {
		cache->sync(cache);
		cache->destroy(cache);
	}

	if (pthread_mutex_unlock(&smfMutex))
		syslog(LOG_ERR, TAG_FORMAT "mutex unlock in atExitCleanUp() failed: %s (%d) ", 0, smfNoQueue, strerror(errno), errno);

	smfAtExitCleanUp();
}

void
printVersion(void)
{
	printf(MILTER_NAME " " MILTER_VERSION " " MILTER_COPYRIGHT "\n");
	printf("LibSnert %s %s", LIBSNERT_VERSION, LIBSNERT_COPYRIGHT "\n");
#ifdef _BUILT
	printf("Built on " _BUILT "\n");
#endif
}

void
printInfo(void)
{
#ifdef MILTER_NAME
	printVar(0, "MILTER_NAME", MILTER_NAME);
#endif
#ifdef MILTER_VERSION
	printVar(0, "MILTER_VERSION", MILTER_VERSION);
#endif
#ifdef MILTER_COPYRIGHT
	printVar(0, "MILTER_COPYRIGHT", MILTER_COPYRIGHT);
#endif
#ifdef MILTER_CONFIGURE
	printVar(LINE_WRAP, "MILTER_CONFIGURE", MILTER_CONFIGURE);
#endif
#ifdef _BUILT
	printVar(0, "MILTER_BUILT", _BUILT);
#endif
#ifdef LIBSNERT_VERSION
	printVar(0, "LIBSNERT_VERSION", LIBSNERT_VERSION);
#endif
#ifdef LIBSNERT_BUILD_HOST
	printVar(LINE_WRAP, "LIBSNERT_BUILD_HOST", LIBSNERT_BUILD_HOST);
#endif
#ifdef LIBSNERT_CONFIGURE
	printVar(LINE_WRAP, "LIBSNERT_CONFIGURE", LIBSNERT_CONFIGURE);
#endif
#ifdef SQLITE_VERSION
	printVar(0, "SQLITE3_VERSION", SQLITE_VERSION);
#endif
#ifdef MILTER_CFLAGS
	printVar(LINE_WRAP, "CFLAGS", MILTER_CFLAGS);
#endif
#ifdef MILTER_LDFLAGS
	printVar(LINE_WRAP, "LDFLAGS", MILTER_LDFLAGS);
#endif
#ifdef MILTER_LIBS
	printVar(LINE_WRAP, "LIBS", MILTER_LIBS);
#endif
}

int
main(int argc, char **argv)
{
	int argi;

	/* Default is OFF. */
	smfOptAccessDb.initial = "";
	smfOptRejectPercentRelay.initial = "-";

	smfOptFile.initial = MILTER_CF;
	smfOptPidFile.initial = PID_FILE;
	smfOptRunUser.initial = RUN_AS_USER;
	smfOptRunGroup.initial = RUN_AS_GROUP;
	smfOptWorkDir.initial = WORK_DIR;
	smfOptMilterSocket.initial = "unix:" SOCKET_FILE;

	/* Parse command line options looking for a file= option. */
	optionInit(optTable, smfOptTable, NULL);
	argi = optionArrayL(argc, argv, optTable, smfOptTable, NULL);

	/* Parse the option file followed by the command line options again. */
	if (smfOptFile.string != NULL && *smfOptFile.string != '\0') {
		/* Do NOT reset this option. */
		smfOptFile.initial = smfOptFile.string;
		smfOptFile.string = NULL;

		optionInit(optTable, smfOptTable, NULL);
		(void) optionFile(smfOptFile.string, optTable, smfOptTable, NULL);
		(void) optionArrayL(argc, argv, optTable, smfOptTable, NULL);
	}

	if (opt_version.string != NULL) {
		printVersion();
		exit(EX_USAGE);
	}
	if (opt_info.string != NULL) {
		printInfo();
		exit(EX_USAGE);
	}
	if (smfOptHelp.string != NULL) {
		optionUsageL(optTable, smfOptTable, NULL);
		exit(2);
	}

	if (smfOptQuit.string != NULL) {
		/* Use SIGQUIT signal in order to avoid delays
		 * caused by libmilter's handling of SIGTERM.
		 * smfi_stop() takes too long since it waits
		 * for connections to terminate, which could
		 * be a several minutes or longer.
		 */
		exit(pidKill(smfOptPidFile.string, SIGQUIT) != 0);
	}

	if (smfOptRestart.string != NULL) {
		(void) pidKill(smfOptPidFile.string, SIGQUIT);
		sleep(2);
	}

	if (smfOptDaemon.value && smfStartBackgroundProcess())
		return 1;

	optMxReject.value = setBitWord(isIpBits, optMxReject.string);
	(void) smfi_settimeout((int) smfOptMilterTimeout.value);
	(void) smfSetLogDetail(smfOptVerbose.string);
	optSmtpTimeout.value *= 1000;

	openlog(MILTER_NAME, LOG_PID, LOG_MAIL);

	if (atexit(atExitCleanUp)) {
		syslog(LOG_ERR, "atexit() failed\n");
		return 1;
	}

	if (*smfOptAccessDb.string != '\0') {
		if (smfLogDetail & SMF_LOG_DATABASE)
			smdbSetDebugMask(SMDB_DEBUG_ALL);

		if ((smdbAccess = smdbOpen(smfOptAccessDb.string, 1)) == NULL) {
			syslog(LOG_ERR, "failed to open \"%s\"", smfOptAccessDb.string);
			return 1;
		}
	}

	if (*optCallAheadDb.string != '\0') {
		if (smfLogDetail & SMF_LOG_DATABASE)
			smdbSetDebugMask(SMDB_DEBUG_ALL);

		if ((callAheadDb = smdbOpen(optCallAheadDb.string, 1)) == NULL) {
			syslog(LOG_ERR, "failed to open %s\n", optCallAheadDb.string);
			return 1;
		}
	}

	CacheSetDebug(smfLogDetail & SMF_LOG_CACHE);

	if ((cache = CacheCreate(optCacheType.string, optCacheFile.string)) == NULL) {
		syslog(LOG_ERR, "failed to create cache\n");
		return 1;
	}

	(void) smfSetFileOwner(&milter, optCacheFile.string);

	if (smfLogDetail & SMF_LOG_DNS)
		pdqSetDebug(1);

	if (smfLogDetail & SMF_LOG_SOCKET_ALL)
		socketSetDebug(10);
	else if (smfLogDetail & SMF_LOG_SOCKET_FD)
		socketSetDebug(1);

	if (socketInit()) {
		syslog(LOG_ERR, "socketInit() error\n");
		return 1;
	}

	return smfMainStart(&milter);
}
