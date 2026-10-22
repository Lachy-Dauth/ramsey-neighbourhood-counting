// glue_check: exact clique number of one colour of a full matrix, computed by splitting the vertex
// set into a base part B = {0..n0-1} and the rest X = {n0..n-1}.
// Every c-clique K satisfies K = S u T with S = K cap X a c-clique of X and T a c-clique of B inside
// the common c-neighbourhood of S.  So omega_c = max over c-cliques S of X (including the empty set)
// of |S| + omega_c(B cap N_c(S)).  Each term is computed by an exact branch and bound.
// usage: glue_check matrix.txt n0 colour      prints omega and the maximising S.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
using namespace std;
static const int MAXW = 8;
struct BS { uint64_t w[MAXW]; };
static int N, NW;
static vector<BS> adj;
static inline bool bany(const BS &b) { for (int i = 0; i < NW; i++) if (b.w[i]) return true; return false; }
static inline int bfirst(const BS &b) { for (int i = 0; i < NW; i++) if (b.w[i]) return i * 64 + __builtin_ctzll(b.w[i]); return -1; }
static inline void bdel(BS &b, int x) { b.w[x >> 6] &= ~(1ULL << (x & 63)); }
static inline int bcnt(const BS &b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(b.w[i]); return c; }
static int best;
static void expand(BS P, int d) {
  vector<int> order, col; BS U = P; int c = 0;
  while (bany(U)) { c++; BS Q = U; while (bany(Q)) { int v = bfirst(Q); bdel(Q, v); bdel(U, v); for (int i = 0; i < NW; i++) Q.w[i] &= ~adj[v].w[i]; order.push_back(v); col.push_back(c); } }
  for (int k = (int)order.size() - 1; k >= 0; k--) {
    if (d + col[k] <= best) return;
    int v = order[k]; BS NP; for (int i = 0; i < NW; i++) NP.w[i] = P.w[i] & adj[v].w[i];
    if (!bany(NP)) { if (d + 1 > best) best = d + 1; } else expand(NP, d + 1);
    bdel(P, v);
  }
}
static int omega_of(const BS &P, int lower) { best = lower; if (bany(P)) expand(P, 0); return best; }
int n0, colr, overall = -1; vector<int> overallS; vector<int> curS; long long nS = 0;
static void recX(int start, BS common) {
  // curS is a clique of X; common = B cap N(curS)
  nS++;
  int need = overall - (int)curS.size();  // only care whether omega(common) > need
  int lower = need < 0 ? 0 : need;
  int w = omega_of(common, lower);
  if (w > lower || overall < 0) {
    if ((int)curS.size() + w > overall) { overall = curS.size() + w; overallS = curS; }
  }
  for (int x = start; x < N; x++) {
    bool ok = true;
    for (int y : curS) if (!((adj[y].w[x >> 6] >> (x & 63)) & 1)) { ok = false; break; }
    if (!ok) continue;
    BS c2; for (int i = 0; i < NW; i++) c2.w[i] = common.w[i] & adj[x].w[i];
    curS.push_back(x); recX(x + 1, c2); curS.pop_back();
  }
}
int main(int argc, char **argv) {
  if (argc != 4) { fprintf(stderr, "usage: glue_check matrix n0 colour\n"); return 2; }
  ifstream in(argv[1]); vector<string> a; string row; while (in >> row) a.push_back(row);
  N = a.size(); NW = (N + 63) / 64; n0 = atoi(argv[2]); colr = atoi(argv[3]);
  for (int i = 0; i < N; i++) { if ((int)a[i].size() != N) { fprintf(stderr, "bad shape\n"); return 2; }
    for (int j = 0; j < N; j++) if (i != j && a[i][j] != a[j][i]) { fprintf(stderr, "asymmetric\n"); return 2; } }
  adj.assign(N, BS());
  for (int u = 0; u < N; u++) { memset(adj[u].w, 0, sizeof(adj[u].w)); for (int v = 0; v < N; v++) if (u != v && a[u][v] == '0' + colr) adj[u].w[v >> 6] |= 1ULL << (v & 63); }
  BS B; memset(B.w, 0, sizeof(B.w)); for (int v = 0; v < n0; v++) B.w[v >> 6] |= 1ULL << (v & 63);
  recX(n0, B);
  printf("n=%d n0=%d colour=%d clique_number=%d (cliques S of X examined: %lld) maximising S:", N, n0, colr, overall, nS);
  for (int x : overallS) printf(" %d", x); printf("\n");
  return 0;
}
