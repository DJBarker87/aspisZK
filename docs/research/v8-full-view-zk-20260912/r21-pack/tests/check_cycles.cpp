#include "model_cycles.hpp"
#include <random>
std::vector<std::vector<int>> decomposition(const Transport& t) {
 std::array<bool,1024> seen{};std::vector<std::vector<int>> out;
 for(int i=0;i<1024;i++) if(!seen[i]) {
  std::vector<int> c; int j=i;
  do {assert(!seen[j]);seen[j]=true;c.push_back(j);j=t.p[j];}while(j!=i);
  if(c.size()>1)out.push_back(c);
 }
 return out;
}
F correction(const std::vector<std::vector<int>>&cs,const V&w,const V&v) {
 F out;
 for(const auto& c:cs) for(size_t k=1;k<c.size();k++)
  out=out+(w[c[k]]-w[c[0]])*(v[c[k-1]]-v[c[k]]);
 return out;
}
int main(){
 Transport old(2),t(3);
 for(int i=0;i<89;i++)assert(t.p[i]==old.p[i]);
 auto cs=decomposition(t);assert(cs.size()==74);
 size_t moved=0,rank=0;
 for(const auto&c:cs){moved+=c.size();rank+=c.size()-1;assert(c.size()<=4);}
 assert(moved==163&&rank==89);
 V weight(1024);for(int i=0;i<1024;i++)weight[i]=parameter(103+i*7);
 for(int i=0;i<1024;i++){
  V m(1024);m[i]=parameter(i+17);auto code=t.forward(m);
  assert(t.inverse(code)==m);assert(dot(weight,m)==dot(t.dual(weight),code));
 }
 for(int i=0;i<89;i++){
  V m(1024);m[t.p[i]]=F(1);m[1023]=-F(1);auto code=t.forward(m);
  for(int j=0;j<1024;j++)assert(code[j]==F(j==i?1:0));
 }
 std::mt19937 rng(0x21);
 for(int sample=0;sample<128;sample++){
  V w(1024),v(1024);
  for(int j=0;j<1024;j++){w[j]=parameter(rng()%10000000);v[j]=parameter(rng()%10000000);}
  F direct;for(int j=0;j<1024;j++)direct=direct+(w[t.p[j]]-w[j])*v[j];
  assert(direct==correction(cs,w,v));
 }
 std::cout<<"{\"transport_basis_cases\":1024,\"pad_images\":89,\"arbitrary_correction_cases\":128,\"changed_coordinates\":163,\"nontrivial_cycles\":74,\"correction_rank\":89,\"max_cycle_length\":4}"<<std::endl;
}
