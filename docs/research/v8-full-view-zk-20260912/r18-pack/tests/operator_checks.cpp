// Uses the same explicit natural-basis chord as the rank probe, but checks
// the sparse terminal against its independently applied adjoint definition.
#define main structural_probe_main
#include "structural_probe.cpp"
#undef main
using Four=std::array<F,4>;
std::vector<std::pair<int,F>> edges(int j){std::vector<std::pair<int,F>>out;int r=j,k=0;F s(1);while(r&(1<<k)){r^=1<<k;s=s.half();out.push_back({r,s});k++;}out.push_back({r|(1<<k),s});return out;}
std::array<F,16> basis(F a,F b){auto a2=a*a,b2=b*b;Four ap={F(1),a2*a,a2,a},bp={F(1),b2*b,b2,b};std::array<F,16>o;for(int j=0;j<16;j++)o[j]=ap[j&3]*bp[j>>2];return o;}
struct SparseKernel{
 std::array<F,16> n{},h{};std::array<F,3> c{};
 SparseKernel(std::array<F,3>abc,std::array<F,4>alphas){auto low=basis(alphas[0],alphas[1]);h=basis(alphas[2],alphas[3]);std::array<F,16>xn{},xc{},yn{},yc{};
 for(int i=0;i<16;i++){int y=i&1,j=i>>1;for(auto rs:edges(j)){int r=rs.first;F s=rs.second;int d=2*(r%8)+y;if(r<8)xn[d]=xn[d]+low[i]*s;else xc[d]=xc[d]+low[i]*s;}
 if(!y)yn[i+1]=yn[i+1]+low[i];else{yn[i-1]=yn[i-1]+low[i].half();for(auto rs:edges(j>>1)){int r=rs.first;F s=rs.second;int line=(r<<1)|(j&1),d=2*(line%8);F v=(low[i]*s).half();if(line<8)yn[d]=yn[d]-v;else yc[d]=yc[d]-v;}}}
 for(int i=0;i<16;i++){n[i]=abc[0]*low[i]+abc[1]*xn[i]+abc[2]*yn[i];}c={abc[1]*xc[0]+abc[2]*yc[0],abc[1]*xc[1],abc[2]*yc[2]};
 }
 Four sparse(const std::vector<int>&s,const V&coins)const{assert(s.size()==coins.size());std::array<std::pair<F,F>,64>sums{};for(size_t i=0;i<s.size();i++){int b=s[i]/16,j=s[i]%16;sums[b].first=sums[b].first+coins[i]*n[j];if(j<3)sums[b].second=sums[b].second+coins[i]*c[j];}Four out{};
 for(int j=0;j<64;j++){F v=sums[j].first;for(auto rs:edges(j))if(rs.first<64)v=v+sums[rs.first].second*rs.second;out[j>>4]=out[j>>4]+v*h[j&15];}
 for(auto&v:out){for(int j=0;j<8;j++){v=v.half();}}return out;}
 Four sparse_nested(const std::vector<int>&s,const V&coins)const{
  std::array<std::pair<F,F>,64>sums{};
  for(size_t i=0;i<s.size();i++){int b=s[i]/16,j=s[i]%16;sums[b].first=sums[b].first+coins[i]*n[j];if(j<3)sums[b].second=sums[b].second+coins[i]*c[j];}
  Four out{};
  for(unsigned j=0;j<64;j++){unsigned bits=0;while(j&(1U<<bits))bits++;F v=j+1<64?sums[j+1].second:F();while(bits){--bits;unsigned row=j&~((1U<<(bits+1))-1);v=(v+sums[row].second).half();}v=v+sums[j].first;out[j>>4]=out[j>>4]+v*h[j&15];}
  for(auto&v:out)for(int j=0;j<8;j++)v=v.half();
  return out;
 }
};
Four direct(const std::vector<int>&s,const V&coins,std::array<F,3>abc,std::array<F,4>alphas){auto lo=basis(alphas[0],alphas[1]),hi=basis(alphas[2],alphas[3]);Four out{};
 for(int b=0;b<4;b++){V q(1024);for(int j=0;j<256;j++){q[256*b+j]=lo[j&15]*hi[j>>4];for(int k=0;k<8;k++)q[256*b+j]=q[256*b+j].half();}auto c=chord_full(q,abc);for(size_t i=0;i<s.size();i++)out[b]=out[b]+c[s[i]]*coins[i];}return out;}
std::array<F,10> transformed_point(std::array<F,10>z){std::array<F,10>p;for(int i=0;i<4;i++)p[i]=F(1)-z[i+6];for(int i=4;i<10;i++)p[i]=z[i-4];return p;}
int main(){
 auto s=slots("stride3");int cases=0;for(int seed=0;seed<24;seed++){std::array<F,4>a;std::array<F,3>abc;for(int j=0;j<4;j++)a[j]=seed==0?F():seed==1?F(1):parameter(seed*17+j+31);for(int j=0;j<3;j++)abc[j]=seed==2?F():parameter(seed*19+j+37);SparseKernel k(abc,a);V coins(271);for(int j=0;j<271;j++)coins[j]=parameter(seed*79+j+3);assert(k.sparse(s,coins)==direct(s,coins,abc,a));assert(k.sparse_nested(s,coins)==k.sparse(s,coins));cases++;}
 for(int i=0;i<271;i++){V coins(271);coins[i]=parameter(91);std::array<F,3>abc={parameter(2),parameter(3),parameter(5)};std::array<F,4>a={parameter(7),parameter(11),parameter(13),parameter(17)};assert(SparseKernel(abc,a).sparse(s,coins)==direct(s,coins,abc,a));assert(SparseKernel(abc,a).sparse_nested(s,coins)==direct(s,coins,abc,a));cases++;}
 Transport old(false);int codec=0;for(int seed=1;seed<=32;seed++){V m(1024);for(int j=0;j<1024;j++)m[j]=parameter(seed*71+j);F sum;for(int r=0;r<1023;r++)if(inactive(r))sum=sum+m[r];m[1023]=-sum;auto c=old.forward(m);assert(c[1023]==F());V selected,rest;std::array<bool,1024>used{};for(int j:s){selected.push_back(c[j]);used[j]=true;}for(int j=0;j<1023;j++)if(!used[j])rest.push_back(c[j]);assert(rest.size()==752);V back(1024);for(size_t i=0;i<s.size();i++)back[s[i]]=selected[i];int at=0;for(int j=0;j<1023;j++)if(!used[j])back[j]=rest[at++];assert(old.inverse(back)==m);
 V weights(1024);auto z=std::array<F,10>{};for(int j=0;j<10;j++)z[j]=parameter(seed*7+j+1);auto a=coinweights(z);for(int i=0;i<271;i++)weights[old.p[s[i]]]=a[i];assert(dot(weights,m)==dot(a,selected));auto transformed=old.dual(weights);for(int j=0;j<1024;j++)assert(transformed[j]==(used[j]?weights[old.p[j]]:F()));
 auto w=mle(z),v=mle(transformed_point(z));for(int j=0;j<1024;j++)assert(v[j]==w[affine_order(j)]);
 // Full two-channel identity for arbitrary vectors: never discard G channel.
 V r(1024),g(1024),b(1024),e(1024),h(1024);for(int j=0;j<1024;j++){r[j]=parameter(j+seed);g[j]=parameter(2*j+seed);b[j]=parameter(3*j+seed);e[j]=parameter(5*j+seed);h[j]=parameter(7*j+seed);}
 F lhs,rhs;for(int j=0;j<1024;j++){lhs=lhs+r[j]*(b[j]+e[j])+g[j]*(b[j]+h[j]);rhs=rhs+(r[j]+g[j])*b[j]+r[j]*e[j]+g[j]*h[j];}assert(lhs==rhs);codec++;}
 Transport minimal(2);std::vector<int>all(1024),changed;std::iota(all.begin(),all.end(),0);for(int j=0;j<1024;j++)if(minimal.p[j]!=j)changed.push_back(j);assert(changed.size()==163);
 for(int seed=1;seed<=16;seed++){V w(1024),delta,J(1024);for(int j=0;j<1024;j++){w[j]=parameter(seed*101+j);J[j]=(minimal.p[j]!=1023&&inactive(minimal.p[j]))?F(1):F();}for(int j:changed)delta.push_back(w[minimal.p[j]]-w[j]);std::array<F,3>abc={parameter(seed+2),parameter(seed+3),parameter(seed+5)};std::array<F,4>a={parameter(seed+7),parameter(seed+11),parameter(seed+13),parameter(seed+17)};
  auto left=direct(all,minimal.dual(w),abc,a),base=direct(all,w,abc,a),d=SparseKernel(abc,a).sparse_nested(changed,delta),mask=SparseKernel(abc,a).sparse_nested(all,J);for(int j=0;j<4;j++)assert(left[j]==base[j]+d[j]-w[1023]*mask[j]);
 }
 std::cout<<"{\"sparse_terminal_cases\":"<<cases<<",\"codec_and_dual_cases\":"<<codec<<",\"retained_coordinates\":752,\"tensor_entry_comparisons\":32768,\"two_channel_pairings\":32,\"minimal_transport_contractions\":16,\"minimal_support\":163,\"all_passed\":true,\"cu_measured\":false}\n";
}
