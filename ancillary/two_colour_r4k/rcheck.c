/* rcheck.c : independent exact checker for two-colour Ramsey lower-bound witnesses.
 *
 *   rcheck <graphfile> <s> <t> [threads] [stopfail]
 *   (stopfail: stop after the first violation found; used for negative controls)
 *
 * Graph file: first token n, then the n x n adjacency matrix as characters '0'/'1'
 * (whitespace ignored).  The program checks, from the definitions:
 *   (a) the matrix is n x n, symmetric, with zero diagonal;
 *   (b) G contains no clique on s vertices;
 *   (c) G contains no independent set on t vertices (= no clique on t vertices in the complement).
 * If (a)-(c) hold, G certifies R(s,t) > n.  Prints PASS or FAIL, and for a FAIL an explicit
 * clique / independent set, which is re-verified pairwise before printing.
 *
 * Search (written independently of the generating code): a clique of size k exists iff for
 * some vertex v (its first vertex in a fixed order) the set P of later neighbours of v contains a
 * clique of size k-1.  expand(P, need) greedily colours P (each colour class is an independent
 * set); vertices are then examined in reverse colour order; when the current colour c is < need
 * the remaining candidates (all of colour <= c) are covered by c independent sets and hence
 * contain no clique of size need, so the branch is closed.  Every branch is either explored or
 * closed by this argument, so a "no" answer is exhaustive.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>

typedef uint64_t u64;
static int n, W;
static u64 *ADJ;          /* current graph being searched */
static int K;             /* clique size searched */
static atomic_int next_root;
static atomic_int found;
static atomic_llong nodes;
static int *witness;
static pthread_mutex_t mx = PTHREAD_MUTEX_INITIALIZER;
static int *order;        /* order[i] = vertex at position i */

static inline u64 *row(u64 *A, int v) { return A + (size_t)v * W; }
static inline int tst(const u64 *b, int i) { return (b[i >> 6] >> (i & 63)) & 1; }
static inline void setb(u64 *b, int i) { b[i >> 6] |= 1ULL << (i & 63); }
static inline void clrb(u64 *b, int i) { b[i >> 6] &= ~(1ULL << (i & 63)); }
static int popc(const u64 *b) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(b[i]); return c; }

typedef struct { u64 *buf; int *vl, *cl; int *stack; int depth; } Ctx;

static int expand(Ctx *cx, int lvl, const u64 *Pin, int need) {
    atomic_fetch_add_explicit(&nodes, 1, memory_order_relaxed);
    if (need == 0) return 1;
    if (atomic_load_explicit(&found, memory_order_relaxed)) return 0;
    u64 *P = cx->buf + (size_t)(3 * lvl) * W, *U = P + W, *Q = U + W;
    memcpy(P, Pin, W * sizeof(u64));
    int cnt = popc(P);
    if (cnt < need) return 0;
    int *vl = cx->vl + (size_t)lvl * n, *cl = cx->cl + (size_t)lvl * n;
    memcpy(U, P, W * sizeof(u64));
    int m = 0, c = 0;
    while (1) {
        int any = 0;
        for (int i = 0; i < W; i++) if (U[i]) { any = 1; break; }
        if (!any) break;
        c++;
        memcpy(Q, U, W * sizeof(u64));
        for (int i = 0; i < W; i++) {
            while (Q[i]) {
                int v = (i << 6) + __builtin_ctzll(Q[i]);
                clrb(U, v); clrb(Q, v);
                const u64 *r = row(ADJ, v);
                for (int j = 0; j < W; j++) Q[j] &= ~r[j];
                vl[m] = v; cl[m] = c; m++;
            }
        }
    }
    for (int idx = m - 1; idx >= 0; idx--) {
        if (cl[idx] < need) return 0;
        int v = vl[idx];
        const u64 *r = row(ADJ, v);
        /* child candidate set = P n N(v); build in a temp then pass */
        u64 tmp[W];
        for (int j = 0; j < W; j++) tmp[j] = P[j] & r[j];
        cx->stack[lvl + 1] = v;
        if (expand(cx, lvl + 1, tmp, need - 1)) return 1;
        clrb(P, v);
    }
    return 0;
}

static void *worker(void *arg) {
    (void)arg;
    Ctx cx;
    cx.buf = calloc((size_t)3 * (K + 3) * W, sizeof(u64));
    cx.vl = malloc(sizeof(int) * (size_t)n * (K + 2));
    cx.cl = malloc(sizeof(int) * (size_t)n * (K + 2));
    cx.stack = malloc(sizeof(int) * (K + 3));
    u64 *P = calloc(W, sizeof(u64));
    while (!atomic_load(&found)) {
        int i = atomic_fetch_add(&next_root, 1);
        if (i >= n) break;
        int v = order[i];
        memset(P, 0, W * sizeof(u64));
        for (int j = i + 1; j < n; j++) { int u = order[j]; if (tst(row(ADJ, v), u)) setb(P, u); }
        cx.stack[0] = v;
        if (K == 1 || expand(&cx, 0, P, K - 1)) {
            pthread_mutex_lock(&mx);
            if (!atomic_load(&found)) {
                atomic_store(&found, 1);
                for (int d = 0; d < K; d++) witness[d] = cx.stack[d];
            }
            pthread_mutex_unlock(&mx);
            break;
        }
    }
    free(cx.buf); free(cx.vl); free(cx.cl); free(cx.stack); free(P);
    return NULL;
}

/* returns 1 and fills witness if a K-clique exists in A */
static int has_clique(u64 *A, int k, int threads) {
    ADJ = A; K = k;
    atomic_store(&next_root, 0); atomic_store(&found, 0); atomic_store(&nodes, 0);
    /* order: by degree, descending (any order is correct) */
    int *deg = malloc(sizeof(int) * n);
    for (int v = 0; v < n; v++) { deg[v] = popc(row(A, v)); order[v] = v; }
    for (int i = 1; i < n; i++) { int x = order[i], j = i - 1; while (j >= 0 && deg[order[j]] < deg[x]) { order[j + 1] = order[j]; j--; } order[j + 1] = x; }
    free(deg);
    if (k <= 0) return 1;
    pthread_t th[64];
    for (int i = 0; i < threads; i++) pthread_create(&th[i], NULL, worker, NULL);
    for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
    return atomic_load(&found);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: rcheck graph s t [threads]\n"); return 2; }
    int s = atoi(argv[2]), t = atoi(argv[3]);
    int threads = argc > 4 ? atoi(argv[4]) : 1;
    int stopfail = argc > 5 && strcmp(argv[5], "stopfail") == 0;
    if (threads < 1) threads = 1; if (threads > 64) threads = 64;
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    if (fscanf(f, "%d", &n) != 1 || n <= 0) { fprintf(stderr, "bad header\n"); return 2; }
    W = (n + 63) / 64;
    char *M = malloc((size_t)n * n);
    long long got = 0; int ch;
    while ((ch = fgetc(f)) != EOF) {
        if (ch == '0' || ch == '1') { if (got < (long long)n * n) M[got] = (char)ch; got++; }
        else if (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') continue;
        else { fprintf(stderr, "FAIL: bad character %d\n", ch); return 1; }
    }
    fclose(f);
    if (got != (long long)n * n) { printf("FAIL: expected %lld matrix entries, got %lld\n", (long long)n * n, got); return 1; }
    long long edges = 0;
    for (int i = 0; i < n; i++) {
        if (M[(size_t)i * n + i] != '0') { printf("FAIL: nonzero diagonal at %d\n", i); return 1; }
        for (int j = 0; j < n; j++) {
            if (M[(size_t)i * n + j] != M[(size_t)j * n + i]) { printf("FAIL: not symmetric at %d,%d\n", i, j); return 1; }
            if (j > i && M[(size_t)i * n + j] == '1') edges++;
        }
    }
    u64 *A = calloc((size_t)n * W, sizeof(u64)), *C = calloc((size_t)n * W, sizeof(u64));
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) {
        if (M[(size_t)i * n + j] == '1') setb(row(A, i), j); else setb(row(C, i), j);
    }
    order = malloc(sizeof(int) * n);
    witness = malloc(sizeof(int) * (s > t ? s : t) + 8);
    printf("n=%d edges=%lld (s,t)=(%d,%d) threads=%d\n", n, edges, s, t, threads);
    int bad = 0;
    for (int pass = 0; pass < 2; pass++) {
        u64 *X = pass == 0 ? A : C; int k = pass == 0 ? s : t;
        const char *what = pass == 0 ? "clique" : "independent set";
        int r = has_clique(X, k, threads);
        if (r) {
            /* re-verify witness from the raw matrix */
            int ok = 1;
            for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) {
                int u = witness[a], v = witness[b];
                if (u == v) ok = 0;
                char e = M[(size_t)u * n + v];
                if (pass == 0 && e != '1') ok = 0;
                if (pass == 1 && e != '0') ok = 0;
            }
            printf("FOUND %s of size %d%s:", what, k, ok ? "" : " (WITNESS VERIFY FAILED)");
            for (int a = 0; a < k; a++) printf(" %d", witness[a]);
            printf("  [nodes %lld]\n", (long long)atomic_load(&nodes));
            bad = 1;
            if (stopfail) { fflush(stdout); break; }
        } else {
            printf("no %s of size %d  [nodes %lld]\n", what, k, (long long)atomic_load(&nodes));
        }
        fflush(stdout);
    }
    printf(bad ? "FAIL\n" : "PASS: graph certifies R(%d,%d) > %d\n", s, t, n);
    return bad;
}
