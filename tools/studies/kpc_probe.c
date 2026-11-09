// What root buys a counter read on this Mac.
//
// Three questions, each answered by a measurement, as far as the running
// user's privileges allow (every refusal is printed with its errno):
//
// 1. Can user code read the core's counters directly? `mrs` of Apple's
//    PMC0/PMC1 and of the architectural PMCCNTR_EL0, under a SIGILL
//    handler, before and after kpc counting is on.
// 2. What does one read cost through each interface: the wall clock
//    (clock_gettime_nsec_np(CLOCK_UPTIME_RAW)), thread_selfcounts (what
//    bench-hashes' clocks crate uses), and kpc_get_thread_counters (root)?
//    Mean wall ns per read over 200,000 reads; cycles and instructions per
//    read where a counter is available.
// 3. With the configurable counters: our samplers' bracket (counts, wall,
//    work, wall, counts) around no work, ~1 us and ~10 us of register
//    arithmetic, 20,000 samples each: min/p50/mean/p95/max of cycles,
//    instructions, and the configured events.
//
// kperf and kperfdata are private frameworks; their functions are resolved
// at run time, and the program says which are missing.
#include <dlfcn.h>
#include <errno.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define KPC_CLASS_FIXED_MASK (1u << 0)
#define KPC_CLASS_CONFIGURABLE_MASK (1u << 1)
#define KPC_MAX_COUNTERS 32

typedef uint64_t kpc_config_t;
static int (*kpc_force_all_ctrs_set)(int);
static int (*kpc_set_counting)(uint32_t);
static int (*kpc_set_thread_counting)(uint32_t);
static int (*kpc_set_config)(uint32_t, kpc_config_t *);
static uint32_t (*kpc_get_counter_count)(uint32_t);
static uint32_t (*kpc_get_config_count)(uint32_t);
static int (*kpc_get_thread_counters)(uint32_t, uint32_t, void *);
typedef struct kpep_db kpep_db;
typedef struct kpep_config kpep_config;
typedef struct kpep_event kpep_event;
static int (*kpep_db_create)(const char *, kpep_db **);
static int (*kpep_db_name)(kpep_db *, const char **);
static int (*kpep_db_events_count)(kpep_db *, size_t *);
static int (*kpep_db_events)(kpep_db *, kpep_event **, size_t);
static int (*kpep_db_event)(kpep_db *, const char *, kpep_event **);
static int (*kpep_event_name)(kpep_event *, const char **);
static int (*kpep_config_create)(kpep_db *, kpep_config **);
static int (*kpep_config_force_counters)(kpep_config *);
static int (*kpep_config_add_event)(kpep_config *, kpep_event **, uint32_t, uint32_t *);
static int (*kpep_config_kpc)(kpep_config *, kpc_config_t *, size_t);
static int (*kpep_config_kpc_count)(kpep_config *, size_t *);
static int (*kpep_config_kpc_classes)(kpep_config *, uint32_t *);
static int (*kpep_config_kpc_map)(kpep_config *, size_t *, size_t);

extern int thread_selfcounts(int kind, void *dst, size_t size);
extern uint64_t clock_gettime_nsec_np(clockid_t clock_id);
#define THSC_TIME_CPI_PER_PERF_LEVEL 4
struct thsc_time_cpi { uint64_t instructions, cycles, user_time, system_time; };

static uint64_t wall(void) { return clock_gettime_nsec_np(CLOCK_UPTIME_RAW); }

static void *need(void *lib, const char *name) {
    void *f = dlsym(lib, name);
    if (!f) { printf("missing symbol %s\n", name); exit(2); }
    return f;
}

static void load(void) {
    void *kperf = dlopen("/System/Library/PrivateFrameworks/kperf.framework/kperf", RTLD_LAZY);
    void *kperfdata = dlopen("/System/Library/PrivateFrameworks/kperfdata.framework/kperfdata", RTLD_LAZY);
    if (!kperf || !kperfdata) { printf("cannot load kperf/kperfdata: %s\n", dlerror()); exit(2); }
    kpc_force_all_ctrs_set = need(kperf, "kpc_force_all_ctrs_set");
    kpc_set_counting = need(kperf, "kpc_set_counting");
    kpc_set_thread_counting = need(kperf, "kpc_set_thread_counting");
    kpc_set_config = need(kperf, "kpc_set_config");
    kpc_get_counter_count = need(kperf, "kpc_get_counter_count");
    kpc_get_config_count = need(kperf, "kpc_get_config_count");
    kpc_get_thread_counters = need(kperf, "kpc_get_thread_counters");
    kpep_db_create = need(kperfdata, "kpep_db_create");
    kpep_db_name = need(kperfdata, "kpep_db_name");
    kpep_db_events_count = need(kperfdata, "kpep_db_events_count");
    kpep_db_events = need(kperfdata, "kpep_db_events");
    kpep_db_event = need(kperfdata, "kpep_db_event");
    kpep_event_name = need(kperfdata, "kpep_event_name");
    kpep_config_create = need(kperfdata, "kpep_config_create");
    kpep_config_force_counters = need(kperfdata, "kpep_config_force_counters");
    kpep_config_add_event = need(kperfdata, "kpep_config_add_event");
    kpep_config_kpc = need(kperfdata, "kpep_config_kpc");
    kpep_config_kpc_count = need(kperfdata, "kpep_config_kpc_count");
    kpep_config_kpc_classes = need(kperfdata, "kpep_config_kpc_classes");
    kpep_config_kpc_map = need(kperfdata, "kpep_config_kpc_map");
}

// 1. Direct reads under a SIGILL handler.
static sigjmp_buf trap;
static void on_sigill(int sig) { (void)sig; siglongjmp(trap, 1); }
static void try_mrs(const char *label, uint64_t (*read)(void)) {
    struct sigaction sa = {0}, old;
    sa.sa_handler = on_sigill;
    sigaction(SIGILL, &sa, &old);
    if (sigsetjmp(trap, 1) == 0) {
        uint64_t a = read(), b = read();
        printf("  %-14s readable: %llu then %llu\n", label, (unsigned long long)a, (unsigned long long)b);
    } else {
        printf("  %-14s SIGILL (no user-mode access)\n", label);
    }
    sigaction(SIGILL, &old, NULL);
}
static uint64_t read_pmc0(void) { uint64_t v; __asm__ volatile("mrs %0, S3_2_C15_C0_0" : "=r"(v)); return v; }
static uint64_t read_pmc1(void) { uint64_t v; __asm__ volatile("mrs %0, S3_2_C15_C1_0" : "=r"(v)); return v; }
static uint64_t read_pmccntr(void) { uint64_t v; __asm__ volatile("mrs %0, PMCCNTR_EL0" : "=r"(v)); return v; }
static void direct_reads(const char *when) {
    printf("direct counter reads, %s:\n", when);
    try_mrs("PMC0 (cycles)", read_pmc0);
    try_mrs("PMC1 (instrs)", read_pmc1);
    try_mrs("PMCCNTR_EL0", read_pmccntr);
}

// 2. The cost of one read.
static int kpc_on = 0;
static uint32_t kpc_n = 0;
static size_t map[KPC_MAX_COUNTERS];
static size_t fixed_cycles_index = (size_t)-1, fixed_instrs_index = (size_t)-1;
static int kpc_read(uint64_t *out) { return kpc_get_thread_counters(0, kpc_n, out); }

static void cost_of(const char *label, void (*read_once)(void)) {
    const uint64_t n = 200000;
    struct thsc_time_cpi before[2] = {0}, after[2] = {0};
    thread_selfcounts(THSC_TIME_CPI_PER_PERF_LEVEL, before, sizeof before);
    uint64_t t = wall();
    for (uint64_t i = 0; i < n; i++) read_once();
    uint64_t w = wall() - t;
    thread_selfcounts(THSC_TIME_CPI_PER_PERF_LEVEL, after, sizeof after);
    printf("  %-28s %4llu ns wall, %5llu P-cycles, %5llu P-instructions per read (means of %llu)\n", label,
        (unsigned long long)((w + n / 2) / n), (unsigned long long)((after[0].cycles - before[0].cycles + n / 2) / n),
        (unsigned long long)((after[0].instructions - before[0].instructions + n / 2) / n), (unsigned long long)n);
}
static void read_wall(void) { volatile uint64_t v = wall(); (void)v; }
static void read_thsc(void) { struct thsc_time_cpi c[2]; thread_selfcounts(THSC_TIME_CPI_PER_PERF_LEVEL, c, sizeof c); }
static void read_kpc(void) { uint64_t c[KPC_MAX_COUNTERS]; kpc_read(c); }

// 3. The bracket around known work.
static uint64_t spin(uint64_t rounds) {
    uint64_t x = 1;
    for (uint64_t i = 0; i < rounds; i++) x = x * 6364136223846793005ull + 1442695040888963407ull;
    __asm__ volatile("" : : "r"(x) : "memory");
    return x;
}
static int cmp(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
static void stats(const char *name, uint64_t *v, size_t n) {
    qsort(v, n, sizeof *v, cmp);
    unsigned __int128 sum = 0;
    for (size_t i = 0; i < n; i++) sum += v[i];
    printf("  %-26s min %8llu p50 %8llu mean %8llu p95 %8llu max %10llu\n", name, (unsigned long long)v[0], (unsigned long long)v[n / 2],
        (unsigned long long)((sum + n / 2) / n), (unsigned long long)v[n * 95 / 100], (unsigned long long)v[n - 1]);
}
static const char *event_names[KPC_MAX_COUNTERS];
static size_t event_count = 0;
static void bracket(const char *label, uint64_t rounds) {
    enum { SAMPLES = 20000 };
    static uint64_t cols[KPC_MAX_COUNTERS + 1][SAMPLES];
    printf("%s, counts outside wall (the samplers' order), %d samples:\n", label, SAMPLES);
    for (size_t s = 0; s < SAMPLES; s++) {
        uint64_t before[KPC_MAX_COUNTERS], after[KPC_MAX_COUNTERS];
        kpc_read(before);
        uint64_t t = wall();
        spin(rounds);
        uint64_t w = wall() - t;
        kpc_read(after);
        cols[0][s] = w;
        for (size_t e = 0; e < event_count; e++) cols[e + 1][s] = after[map[e]] - before[map[e]];
    }
    stats("wall ns", cols[0], SAMPLES);
    for (size_t e = 0; e < event_count; e++) stats(event_names[e], cols[e + 1], SAMPLES);
}

static int configure(void) {
    int r = kpc_force_all_ctrs_set(1);
    if (r != 0) { printf("kpc_force_all_ctrs_set(1): %d, errno %d (%s); the rest needs root\n", r, errno, strerror(errno)); return 0; }
    kpep_db *db = NULL;
    if (kpep_db_create(NULL, &db) != 0) { printf("kpep_db_create failed\n"); return 0; }
    const char *name = "?"; size_t n = 0;
    kpep_db_name(db, &name); kpep_db_events_count(db, &n);
    printf("event database: %s, %zu events\n", name, n);
    kpep_event **all = calloc(n, sizeof *all);
    kpep_db_events(db, all, n * sizeof *all);
    printf("events:");
    for (size_t i = 0; i < n; i++) { const char *en = "?"; kpep_event_name(all[i], &en); printf(" %s", en); }
    printf("\n");
    // The fixed two, then the stall and miss events this question needs,
    // whichever of these names the database has.
    const char *wanted[] = {"FIXED_CYCLES", "FIXED_INSTRUCTIONS", "L1D_CACHE_MISS_LD", "L1D_CACHE_MISS_ST", "L1D_TLB_MISS", "L2_TLB_MISS",
        "L1I_CACHE_MISS_DEMAND", "MAP_STALL_DISPATCH", "MAP_STALL", "BRANCH_MISPRED_NONSPEC", "INTERRUPT_PENDING"};
    kpep_config *cfg = NULL;
    if (kpep_config_create(db, &cfg) != 0 || kpep_config_force_counters(cfg) != 0) { printf("kpep_config_create/force_counters failed\n"); return 0; }
    for (size_t i = 0; i < sizeof wanted / sizeof *wanted; i++) {
        kpep_event *ev = NULL;
        if (kpep_db_event(db, wanted[i], &ev) != 0) { printf("  no event %s here\n", wanted[i]); continue; }
        uint32_t err = 0;
        if (kpep_config_add_event(cfg, &ev, 0, &err) != 0) { printf("  cannot add %s (error %u: counters full or incompatible)\n", wanted[i], err); continue; }
        event_names[event_count++] = wanted[i];
    }
    uint32_t classes = 0; size_t reg_count = 0;
    kpep_config_kpc_classes(cfg, &classes);
    kpep_config_kpc_count(cfg, &reg_count);
    kpc_config_t regs[KPC_MAX_COUNTERS] = {0};
    if (kpep_config_kpc(cfg, regs, reg_count * sizeof *regs) != 0) { printf("kpep_config_kpc failed\n"); return 0; }
    if (kpep_config_kpc_map(cfg, map, sizeof map) != 0) { printf("kpep_config_kpc_map failed\n"); return 0; }
    if (kpc_set_config(classes, regs) != 0) { printf("kpc_set_config: errno %d\n", errno); return 0; }
    if (kpc_set_counting(classes) != 0) { printf("kpc_set_counting: errno %d\n", errno); return 0; }
    if (kpc_set_thread_counting(classes) != 0) { printf("kpc_set_thread_counting: errno %d\n", errno); return 0; }
    kpc_n = kpc_get_counter_count(classes);
    printf("counting classes 0x%x, %u counters; configured:", classes, kpc_n);
    for (size_t e = 0; e < event_count; e++) printf(" %s@%zu", event_names[e], map[e]);
    printf("\n");
    kpc_on = 1;
    return 1;
}

int main(void) {
    printf("uid %d euid %d\n", getuid(), geteuid());
    load();
    printf("kpc counters: %u fixed, %u configurable (%u config registers)\n", kpc_get_counter_count(KPC_CLASS_FIXED_MASK),
        kpc_get_counter_count(KPC_CLASS_CONFIGURABLE_MASK), kpc_get_config_count(KPC_CLASS_CONFIGURABLE_MASK));
    direct_reads("before any kpc setup");
    printf("cost of one read:\n");
    cost_of("wall (CLOCK_UPTIME_RAW)", read_wall);
    cost_of("thread_selfcounts", read_thsc);
    if (!configure()) return 0;
    direct_reads("with kpc counting on");
    printf("cost of one read, kpc on:\n");
    cost_of("wall (CLOCK_UPTIME_RAW)", read_wall);
    cost_of("thread_selfcounts", read_thsc);
    cost_of("kpc_get_thread_counters", read_kpc);
    uint64_t t = wall();
    spin(1000000);
    uint64_t per_million = wall() - t;
    uint64_t per_us = 1000000000ull / (per_million ? per_million : 1);
    printf("spin: %llu ns per 1e6 rounds; %llu rounds per us\n", (unsigned long long)per_million, (unsigned long long)per_us);
    bracket("no work", 0);
    bracket("~1 us", per_us);
    bracket("~10 us", 10 * per_us);
    kpc_set_thread_counting(0);
    kpc_set_counting(0);
    kpc_force_all_ctrs_set(0);
    return 0;
}
