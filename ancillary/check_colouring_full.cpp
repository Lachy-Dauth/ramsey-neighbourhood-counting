#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
// Independent direct adjacency-matrix clique decision. No seed assumptions or symmetry.
struct Checker {
 vector<string> a; char colour; unsigned long long nodes=0;
 bool adjacent(int x,int y) { return x!=y && a[x][y]==colour; }
 bool exists(vector<int> cand,int need) {
  ++nodes;
  if(need==0) return true;
  if((int)cand.size()<need) return false;
  if(need==1) return !cand.empty();
  if(need==2) {for(size_t i=0;i<cand.size();++i) for(size_t j=i+1;j<cand.size();++j) if(adjacent(cand[i],cand[j]))return true; return false;}
  // Proper greedy colouring of the induced candidate graph bounds its clique number.
  vector<vector<int>> classes;
  for(int v:cand) {
   size_t c=0;
   for(;c<classes.size();++c) {bool ok=true;for(int w:classes[c]) if(adjacent(v,w)){ok=false;break;}if(ok)break;}
   if(c==classes.size())classes.emplace_back();classes[c].push_back(v);
  }
  if((int)classes.size()<need)return false;
  // Enumerate the highest numbered remaining vertex, then only its earlier neighbours.
  while((int)cand.size()>=need) {
   int v=cand.back();cand.pop_back(); vector<int> next;
   for(int w:cand)if(adjacent(v,w))next.push_back(w);
   if(exists(next,need-1))return true;
  }
  return false;
 }
};
int main(int argc,char** argv){
 if(argc!=5){cerr<<"usage: checker matrix k0 k1 k2\n";return 2;}
 ifstream input(argv[1]);if(!input){cerr<<"input missing\n";return 2;}
 Checker c;string row;while(input>>row)c.a.push_back(row);int n=c.a.size();
 if(!n){cerr<<"empty input\n";return 2;}
 for(int i=0;i<n;++i){if(c.a[i].size()!=n){cerr<<"bad shape\n";return 2;}for(int j=0;j<n;++j){if(c.a[i][j]<'0'||c.a[i][j]>'2'||c.a[i][j]!=c.a[j][i]){cerr<<"bad matrix\n";return 2;}}}
 bool all=true;
 for(int col=0;col<3;++col){c.colour='0'+col;c.nodes=0;vector<int> cand(n);iota(cand.begin(),cand.end(),0);
  // Independent ordering by colour-degree, with deterministic vertex tie-break.
  stable_sort(cand.begin(),cand.end(),[&](int x,int y){return count(c.a[x].begin(),c.a[x].end(),c.colour)<count(c.a[y].begin(),c.a[y].end(),c.colour);});
  auto start=chrono::steady_clock::now();bool bad=c.exists(cand,stoi(argv[col+2]));double seconds=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cout<<"{\"file\":\""<<argv[1]<<"\",\"n\":"<<n<<",\"colour\":"<<col<<",\"forbidden\":"<<argv[col+2]<<",\"clique_found\":"<<(bad?"true":"false")<<",\"nodes\":"<<c.nodes<<",\"seconds\":"<<seconds<<"}"<<endl;all &= !bad;
 }
 return all?0:1;
}
