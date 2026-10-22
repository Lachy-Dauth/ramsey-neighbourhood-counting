/* qpsym.c : exact check that a vertex set S meets every independent k-set of the power-residue
 * graph Q_p (vertices Z_p, x ~ y iff x - y is a nonzero e-th power), using its affine symmetry.
 *
 *   qpsym <p> <e> <k> <delfile|-> [threads] [repsout]
 *
 * Built from the definitions (independently of the generating code):
 *  - R = { x^e : x in Z_p^* }; requires -1 in R (so Q_p is undirected).
 *  - For a in R and b in Z_p, x -> a x + b is an automorphism (a R = R is verified explicitly).
 *  - The orbits of R acting on Z_p^* by multiplication are the cosets of R.  Let O_1, ..., O_m be the
 *    cosets of R different from R itself (these are exactly the non-neighbours of 0 other than 0), in
 *    a fixed order, with representatives r_j = smallest element of O_j.
 *  - Lemma: every independent k-set J (k >= 2) is the image under some x -> a x + b (a in R) of an
 *    independent k-set I with 0, r_j in I and I disjoint from O_1 u ... u O_{j-1}, for some j.
 *    Proof: translate an element u of J to 0; the image J' contains 0, so J' \ {0} lies in
 *    O_1 u ... u O_m; let j be least with J' meeting O_j, pick y in J' n O_j, and multiply by a in R
 *    with a y = r_j (exists since O_j = y R).  Multiplication fixes every coset, so the image still
 *    misses O_1..O_{j-1}.
 *  - The program enumerates ALL such representatives I (independent (k-2)-sets inside the common
 *    non-neighbourhood of 0 and r_j, minus earlier cosets) by an exhaustive clique search with a
 *    greedy-colouring bound, and then checks that a I + b meets S for every a in R, b in Z_p:
 *    for fixed a, the bad b are those outside U_a = union over i in I of (S - a i).
 *  - Output: number of representatives; "ALL HIT" if S meets every independent k-set (then
 *    alpha(Q_p - S) <= k-1), otherwise an explicit independent k-set disjoint from S (re-verified).
 *    With delfile '-', S is empty: then "ALL HIT" happens iff there are no representatives, i.e.
 *    alpha(Q_p) <= k-1.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>

typedef uint64_t u64;
static int p, e, K, W;
static unsigned char *isR;         /* isR[x] = x is a nonzero e-th power */
static u64 *CADJ;                  /* complement adjacency (non-adjacency, no loops) as bitsets */
static inline int tst(const u64 *b, int i) { return (b[i >> 6] >> (i & 63)) & 1; }
static inline void setb(u64 *b, int i) { b[i >> 6] |= 1ULL << (i & 63); }
static inline void clrb(u64 *b, int i) { b[i >> 6] &= ~(1ULL << (i & 63)); }
static inline u64 *crow(int v) { return CADJ + (size_t)v * W; }
static int popc(const u64 *b) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(b[i]); return c; }

/* representatives */
static int *reps = NULL; static long long nreps = 0, capreps = 0;
static pthread_mutex_t mx = PTHREAD_MUTEX_INITIALIZER;
static atomic_llong nodes;

static void addrep(const int *I) {
    pthread_mutex_lock(&mx);
    if (nreps == capreps) { capreps = capreps ? 2 * capreps : 1024; reps = realloc(reps, sizeof(int) * K * capreps); }
    memcpy(reps + nreps * K, I, sizeof(int) * K); nreps++;
    pthread_mutex_unlock(&mx);
}

typedef struct { u64 *buf; int *vl, *cl; int stack[512]; } Ctx;

/* enumerate all cliques of size exactly `need` (more) in the complement inside P */
static void expand(Ctx *cx, int lvl, const u64 *Pin, int need, int depth) {
    atomic_fetch_add_explicit(&nodes, 1, memory_order_relaxed);
    if (need == 0) { addrep(cx->stack); return; }
    u64 *P = cx->buf + (size_t)(2 * lvl) * W, *U = P + W;
    memcpy(P, Pin, W * sizeof(u64));
    if (popc(P) < need) return;
    int *vl = cx->vl + (size_t)lvl * p, *cl = cx->cl + (size_t)lvl * p;
    memcpy(U, P, W * sizeof(u64));
    int m = 0, c = 0;
    u64 Q[W];
    for (;;) {
        int any = 0; for (int i = 0; i < W; i++) if (U[i]) { any = 1; break; }
        if (!any) break;
        c++;
        memcpy(Q, U, W * sizeof(u64));
        for (int i = 0; i < W; i++) while (Q[i]) {
            int v = (i << 6) + __builtin_ctzll(Q[i]);
            clrb(U, v); clrb(Q, v);
            const u64 *r = crow(v);
            for (int j = 0; j < W; j++) Q[j] &= ~r[j];   /* same colour class: pairwise non-adjacent in the searched graph */
            vl[m] = v; cl[m] = c; m++;
        }
    }
    for (int idx = m - 1; idx >= 0; idx--) {
        if (cl[idx] < need) return;
        int v = vl[idx];
        const u64 *r = crow(v);
        u64 T[W];
        for (int j = 0; j < W; j++) T[j] = P[j] & r[j];
        cx->stack[depth] = v;
        expand(cx, lvl + 1, T, need - 1, depth + 1);
        clrb(P, v);
    }
}

/* work items: (j, first vertex v of the (k-2)-set in a fixed order) */
static int nitems; static int *item_r, *item_v; static u64 *item_P; static atomic_int next_item;

static void *worker(void *arg) {
    (void)arg;
    Ctx cx; cx.buf = calloc((size_t)2 * (K + 4) * W, sizeof(u64));
    cx.vl = malloc(sizeof(int) * (size_t)p * (K + 4)); cx.cl = malloc(sizeof(int) * (size_t)p * (K + 4));
    for (;;) {
        int it = atomic_fetch_add(&next_item, 1);
        if (it >= nitems) break;
        cx.stack[0] = 0; cx.stack[1] = item_r[it]; cx.stack[2] = item_v[it];
        expand(&cx, 0, item_P + (size_t)it * W, K - 3, 3);
    }
    free(cx.buf); free(cx.vl); free(cx.cl);
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: qpsym p e k delfile|- [threads] [repsout]\n"); return 2; }
    p = atoi(argv[1]); e = atoi(argv[2]); K = atoi(argv[3]);
    int threads = argc > 5 ? atoi(argv[5]) : 1;
    if (K < 3 || K > 500) { fprintf(stderr, "k out of range\n"); return 2; }
    for (int d = 2; d * d <= p; d++) if (p % d == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    W = (p + 63) / 64;
    isR = calloc(p, 1);
    for (long long x = 1; x < p; x++) { long long y = 1; for (int t = 0; t < e; t++) y = y * x % p; isR[y] = 1; }
    if (!isR[p - 1]) { printf("FAIL: -1 is not an e-th power\n"); return 1; }
    int nR = 0; int *Rl = malloc(sizeof(int) * p);
    for (int x = 1; x < p; x++) if (isR[x]) Rl[nR++] = x;
    /* verify a R = R for all a in R */
    for (int i = 0; i < nR; i++) for (int t = 0; t < nR; t++) if (!isR[(long long)Rl[i] * Rl[t] % p]) { printf("FAIL: R not closed\n"); return 1; }
    /* cosets of R */
    int *coset = malloc(sizeof(int) * p); for (int x = 0; x < p; x++) coset[x] = -1;
    int ncos = 0; int reprs[4096];
    for (int x = 1; x < p; x++) if (coset[x] < 0) {
        for (int i = 0; i < nR; i++) coset[(long long)x * Rl[i] % p] = ncos;
        reprs[ncos++] = x;
    }
    /* coset 0 is R itself (contains 1) */
    if (!isR[reprs[0]]) { printf("FAIL: coset order\n"); return 1; }
    CADJ = calloc((size_t)p * W, sizeof(u64));
    for (int x = 0; x < p; x++) for (int y = 0; y < p; y++) if (x != y && !isR[((x - y) % p + p) % p]) setb(crow(x), y);
    /* S */
    unsigned char *inS = calloc(p, 1); int nS = 0;
    if (strcmp(argv[4], "-") != 0) {
        FILE *f = fopen(argv[4], "r"); if (!f) { perror("delfile"); return 2; }
        char tok[64];
        while (fscanf(f, "%63s", tok) == 1) {
            int dig = 1; for (char *q = tok; *q; q++) if (*q < '0' || *q > '9') dig = 0;
            if (!dig) continue;
            int v = atoi(tok); if (v < 0 || v >= p) { printf("FAIL: bad vertex %d\n", v); return 1; }
            if (!inS[v]) { inS[v] = 1; nS++; }
        }
        fclose(f);
    }
    printf("p=%d e=%d |R|=%d cosets=%d k=%d |S|=%d threads=%d\n", p, e, nR, ncos, K, nS, threads);
    /* build work items */
    nitems = 0; item_r = malloc(sizeof(int) * p * ncos); item_v = malloc(sizeof(int) * p * ncos);
    item_P = calloc((size_t)p * ncos * W, sizeof(u64));
    u64 C[W];
    for (int j = 1; j < ncos; j++) {
        int r = reprs[j];
        memset(C, 0, sizeof C);
        for (int y = 1; y < p; y++) {
            if (y == r) continue;
            if (isR[y]) continue;                 /* must be non-adjacent to 0 */
            if (coset[y] < j) continue;           /* avoid earlier cosets (coset 0 = R already excluded) */
            if (isR[((y - r) % p + p) % p]) continue; /* non-adjacent to r */
            setb(C, y);
        }
        /* split by first vertex in natural order: sets {0, r, v, ...later candidates} */
        for (int v = 0; v < p; v++) if (tst(C, v)) {
            u64 *P = item_P + (size_t)nitems * W;
            for (int u = v + 1; u < p; u++) if (tst(C, u) && tst(crow(v), u)) setb(P, u);
            item_r[nitems] = r; item_v[nitems] = v; nitems++;
        }
    }
    atomic_store(&next_item, 0);
    pthread_t th[64]; if (threads > 64) threads = 64;
    for (int i = 0; i < threads; i++) pthread_create(&th[i], NULL, worker, NULL);
    for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
    printf("representatives (independent %d-sets containing 0 and a coset representative): %lld  [nodes %lld]\n", K, nreps, (long long)atomic_load(&nodes));
    /* re-verify each representative is independent */
    for (long long q = 0; q < nreps; q++) {
        int *I = reps + q * K;
        for (int a = 0; a < K; a++) for (int b = a + 1; b < K; b++) {
            int d = ((I[a] - I[b]) % p + p) % p;
            if (d == 0 || isR[d]) { printf("FAIL: internal error, representative not independent\n"); return 1; }
        }
    }
    if (argc > 6) { FILE *f = fopen(argv[6], "w"); for (long long q = 0; q < nreps; q++) { for (int a = 0; a < K; a++) fprintf(f, a ? " %d" : "%d", reps[q * K + a]); fprintf(f, "\n"); } fclose(f); }
    /* hitting check: for each rep I and a in R, U_a = union_i (S - a i) must be all of Z_p */
    u64 *rot = calloc((size_t)p * W, sizeof(u64));   /* rot[t] = S - t = { s - t } */
    for (int t = 0; t < p; t++) for (int s = 0; s < p; s++) if (inS[s]) setb(rot + (size_t)t * W, ((s - t) % p + p) % p);
    u64 full[W]; memset(full, 0, sizeof full); for (int b = 0; b < p; b++) setb(full, b);
    long long bad = 0;
    for (long long q = 0; q < nreps && !bad; q++) {
        int *I = reps + q * K;
        for (int ai = 0; ai < nR && !bad; ai++) {
            long long a = Rl[ai];
            u64 U[W]; memset(U, 0, sizeof U);
            for (int t = 0; t < K; t++) { const u64 *rr = rot + (size_t)(a * I[t] % p) * W; for (int w = 0; w < W; w++) U[w] |= rr[w]; }
            for (int w = 0; w < W; w++) if ((U[w] & full[w]) != full[w]) {
                int b = -1; for (int z = 0; z < 64; z++) { int bb = w * 64 + z; if (bb < p && !((U[w] >> z) & 1)) { b = bb; break; } }
                /* explicit witness a I + b, re-verified */
                int J[512]; int ok = 1;
                for (int t = 0; t < K; t++) { J[t] = (int)((a * I[t] + b) % p); if (inS[J[t]]) ok = 0; }
                for (int x = 0; x < K; x++) for (int y = x + 1; y < K; y++) { int d = ((J[x] - J[y]) % p + p) % p; if (d == 0 || isR[d]) ok = 0; }
                printf("NOT HIT: independent %d-set disjoint from S%s:", K, ok ? "" : " (WITNESS VERIFY FAILED)");
                for (int t = 0; t < K; t++) printf(" %d", J[t]); printf("\n");
                bad = 1; break;
            }
        }
    }
    if (!bad) printf("ALL HIT: every independent %d-set of Q_%d meets S, so alpha(Q_%d - S) <= %d on %d vertices\n", K, p, p, K - 1, p - nS);
    return bad ? 1 : 0;
}
