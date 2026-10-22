// kcheck: exact clique checker for a 3-colouring given as a full symmetric matrix.
// Written from the definition: colour c contains K_k iff some k vertices are pairwise joined in colour c.
// Usage: kcheck matrix.txt k0 k1 k2      (decides, for each colour c, whether a monochromatic K_{k_c} exists)
//        kcheck matrix.txt -max c        (computes the exact clique number of colour c)
// Matrix: n lines of n characters in {0,1,2}; diagonal ignored. Exit code 0 iff no forbidden clique.
// Search: branch and bound over bitsets, greedy-colouring bound (Tomita-style), no symmetry assumptions.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
#include <iostream>
#include <chrono>
using namespace std;
static const int MAXW = 8; // up to 512 vertices
struct BS { uint64_t w[MAXW]; };
static int N, NW;
static vector<BS> adj;
static long long nodes;
static inline void bclear(BS &b) { memset(b.w, 0, sizeof(b.w)); }
static inline void bset(BS &b, int x) { b.w[x >> 6] |= 1ULL << (x & 63); }
static inline bool btest(const BS &b, int x) { return (b.w[x >> 6] >> (x & 63)) & 1ULL; }
static inline int bcount(const BS &b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(b.w[i]); return c; }
static inline bool bany(const BS &b) { for (int i = 0; i < NW; i++) if (b.w[i]) return true; return false; }
static inline int bfirst(const BS &b) { for (int i = 0; i < NW; i++) if (b.w[i]) return i * 64 + __builtin_ctzll(b.w[i]); return -1; }
static inline void bdel(BS &b, int x) { b.w[x >> 6] &= ~(1ULL << (x & 63)); }

static int best; static vector<int> cur, bestset; static int target; static bool found;
// expand: P = candidate set, all adjacent to every vertex of cur.
static void expand(BS P) {
  nodes++;
  // greedy colouring: order vertices by colour class
  int np = bcount(P);
  vector<int> order; order.reserve(np); vector<int> col; col.reserve(np);
  BS U = P; int c = 0;
  while (bany(U)) {
    c++; BS Q = U;
    while (bany(Q)) {
      int v = bfirst(Q);
      bdel(Q, v); bdel(U, v);
      for (int i = 0; i < NW; i++) Q.w[i] &= ~adj[v].w[i];
      order.push_back(v); col.push_back(c);
    }
  }
  for (int k = (int)order.size() - 1; k >= 0; k--) {
    if ((int)cur.size() + col[k] <= best) return;
    int v = order[k];
    cur.push_back(v);
    BS NP; for (int i = 0; i < NW; i++) NP.w[i] = P.w[i] & adj[v].w[i];
    if (!bany(NP)) {
      if ((int)cur.size() > best) { best = cur.size(); bestset = cur; if (target > 0 && best >= target) { found = true; } }
    } else expand(NP);
    cur.pop_back();
    if (found) return;
    bdel(P, v);
  }
}
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: kcheck matrix k0 k1 k2 | kcheck matrix -max c\n"); return 2; }
  ifstream in(argv[1]); if (!in) { fprintf(stderr, "cannot open\n"); return 2; }
  vector<string> a; string row; while (in >> row) a.push_back(row);
  N = a.size(); NW = (N + 63) / 64;
  if (N == 0 || N > 64 * MAXW) { fprintf(stderr, "bad size\n"); return 2; }
  for (int i = 0; i < N; i++) {
    if ((int)a[i].size() != N) { fprintf(stderr, "bad shape row %d\n", i); return 2; }
    for (int j = 0; j < N; j++) {
      if (i == j) continue;
      if (a[i][j] < '0' || a[i][j] > '2') { fprintf(stderr, "bad entry %d %d\n", i, j); return 2; }
      if (a[i][j] != a[j][i]) { fprintf(stderr, "asymmetric %d %d\n", i, j); return 2; }
    }
  }
  bool maxmode = string(argv[2]) == "-max";
  int ok = 0;
  for (int colr = 0; colr < 3; colr++) {
    if (maxmode && colr != atoi(argv[3])) continue;
    adj.assign(N, BS());
    for (int u = 0; u < N; u++) { bclear(adj[u]); for (int v = 0; v < N; v++) if (u != v && a[u][v] == '0' + colr) bset(adj[u], v); }
    int k = maxmode ? 0 : atoi(argv[2 + colr]);
    target = k; found = false; best = 0; nodes = 0; cur.clear(); bestset.clear();
    auto t0 = chrono::steady_clock::now();
    BS P; bclear(P); for (int v = 0; v < N; v++) bset(P, v);
    // lower bound for pruning in decision mode: we only need to know whether a k-clique exists
    if (!maxmode) best = k - 1; // prune everything that cannot reach k
    expand(P);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    // verify any clique reported
    for (size_t x = 0; x < bestset.size(); x++) for (size_t y = x + 1; y < bestset.size(); y++)
      if (a[bestset[x]][bestset[y]] != '0' + colr) { printf("INTERNAL ERROR: reported clique is not a clique\n"); return 3; }
    if (maxmode) {
      printf("n=%d colour=%d clique_number=%d nodes=%lld seconds=%.2f witness:", N, colr, best, nodes, secs);
      for (int v : bestset) printf(" %d", v); printf("\n");
    } else {
      bool has = found;
      printf("n=%d colour=%d forbidden=K%d clique_found=%s nodes=%lld seconds=%.2f", N, colr, k, has ? "true" : "false", nodes, secs);
      if (has) { printf(" witness:"); for (int v : bestset) printf(" %d", v); }
      printf("\n");
      if (has) ok = 1;
    }
    fflush(stdout);
  }
  return ok;
}
