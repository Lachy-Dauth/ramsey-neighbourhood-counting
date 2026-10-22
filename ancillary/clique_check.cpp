// Independent max-clique check for circulant green graphs (vertex-transitive => cliques through 0 suffice).
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <set>
#include <iostream>
#include <algorithm>
using namespace std;
const int W=5; struct BS{ uint64_t w[W]={0,0,0,0,0};
  bool any()const{for(int i=0;i<W;i++)if(w[i])return true;return false;}
  int first()const{for(int i=0;i<W;i++)if(w[i])return i*64+__builtin_ctzll(w[i]);return -1;}
  void reset(int v){w[v>>6]&=~(1ULL<<(v&63));} void set(int v){w[v>>6]|=1ULL<<(v&63);}
  BS operator&(const BS&o)const{BS r;for(int i=0;i<W;i++)r.w[i]=w[i]&o.w[i];return r;}
  BS andnot(const BS&o)const{BS r;for(int i=0;i<W;i++)r.w[i]=w[i]&~o.w[i];return r;} };
int n; vector<BS> adj; int best=0; long long nodes=0;
void expand(BS P,int size){
    nodes++;
    vector<int> order,colour; BS U=P; int c=0;
    while(U.any()){ c++; BS Q=U; while(Q.any()){ int v=Q.first(); Q.reset(v); Q=Q.andnot(adj[v]); U.reset(v); order.push_back(v); colour.push_back(c);} }
    for(int i=(int)order.size()-1;i>=0;i--){
        if(size+colour[i]<=best) return;
        int v=order[i]; BS NP=P&adj[v];
        if(!NP.any()){ if(size+1>best) best=size+1; } else expand(NP,size+1);
        P.reset(v);
    }
}
int main(){
    int k; cin>>n>>k; set<int> A,Bd; int x;
    while(cin>>x&&x>=0)A.insert(x); while(cin>>x&&x>=0)Bd.insert(x);
    auto dist=[&](int i,int j){int d=abs(i-j);return min(d,n-d);};
    adj.assign(n,BS());
    for(int i=0;i<n;i++)for(int j=0;j<n;j++) if(i!=j){int d=dist(i,j); if(!A.count(d)&&!Bd.count(d)) adj[i].set(j);}
    expand(adj[0],1);
    int tri=0;
    for(int col=0;col<2;col++){ auto &S=col?Bd:A;
      for(int a=1;a<n;a++)for(int b=a+1;b<n;b++) if(S.count(dist(0,a))&&S.count(dist(0,b))&&S.count(dist(a,b))) tri++; }
    printf("n=%d k=%d: max green clique = %d (need < %d); red/blue triangles through 0: %d -> %s  [%lld nodes]\n",
           n,k,best,k,tri,(best<k&&tri==0)?"VALID":"INVALID",nodes);
}
