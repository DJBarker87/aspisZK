// Exact independent model checks. No Aspis/SBF execution is claimed.
#include "model.hpp"
#include "correction_tables.hpp"
#include <limits>
uint64_t state=0x79b151ed67fdbce3ULL;
U next_u(){state^=state<<13;state^=state>>7;state^=state<<17;return U(state%P);}
F random_f(){return Q(C(B(next_u()),B(next_u())),C(B(next_u()),B(next_u())));}
Four factored(const V&lo,const V&hi,const SparseKernel&k){
 std::array<F,100>nc;std::array<F,12>cc;std::array<std::pair<F,F>,64>sums{};
 for(int i=0;i<100;i++)nc[i]=lo[NORMAL_PAIRS[i][0]]*k.n[NORMAL_PAIRS[i][1]];
 for(int i=0;i<12;i++)cc[i]=lo[CARRY_PAIRS[i][0]]*k.c[CARRY_PAIRS[i][1]];
 for(auto&b:NORMAL_BLOCKS){F x;for(int i=b[2];i<b[3];i++){auto&t=NORMAL_TERMS[i];x=t[1]>0?x+nc[t[0]]:x-nc[t[0]];}sums[b[1]].first=sums[b[1]].first+hi[b[0]]*x;}
 for(auto&b:CARRY_BLOCKS){F x;for(int i=b[2];i<b[3];i++){auto&t=CARRY_TERMS[i];x=t[1]>0?x+cc[t[0]]:x-cc[t[0]];}sums[b[1]].second=sums[b[1]].second+hi[b[0]]*x;}
 Four out{};for(int j=0;j<64;j++){F v=sums[j].first;for(auto rs:edges(j))if(rs.first<64)v=v+sums[rs.first].second*rs.second;out[j>>4]=out[j>>4]+v*k.h[j&15];}
 for(auto&v:out)for(int i=0;i<8;i++)v=v.half();return out;
}
V dfold(const V&v,F a){assert(v.size()%4==0);V o(v.size()/4);for(size_t j=0;j<o.size();j++)o[j]=(v[4*j]+a*(v[4*j+3]+a*(v[4*j+2]+a*v[4*j+1]))).half().half();return o;}
V line_basis(F x){V o(256,F(1));std::array<F,8>f;f[0]=x;for(int i=1;i<8;i++)f[i]=F(2)*f[i-1]*f[i-1]-F(1);for(int j=0;j<256;j++)for(int i=0;i<8;i++)if(j&(1<<i))o[j]=o[j]*f[i];return o;}
F fold4(F x,F y,F a,const Four&q){F e=(q[0]+q[1]+q[2]+q[3]).half().half(),by=(q[0]-q[1]-q[2]+q[3])*y.inv(),bx=(q[0]+q[1]-q[2]-q[3])*x.inv(),bxy=(q[0]-q[1]+q[2]-q[3])*(x*y).inv();return e+a*(by+a*(bx+a*bxy)).half().half();}
U addfast(U a,U b){U s=a+b;return s>=P?s-P:s;}
U subfast(U a,U b){U s=a+P-b;return s>=P?s-P:s;}
U mulfast(U a,U b){uint64_t v=uint64_t(a)*b,s=(v&P)+(v>>31);return U(s>=P?s-P:s);}
U halfn(U a,unsigned n){assert(n<=30);return n?((a>>n)|((a&((U(1)<<n)-1))<<(31-n))):a;}
int main(){
 Transport t(2);std::vector<int>support;for(int j=0;j<1024;j++)if(t.p[j]!=j)support.push_back(j);assert(support.size()==163);
 int correction=0,dense=0;for(int c=0;c<192;c++){
  V lo(16),hi(64);for(auto&v:lo)v=random_f();for(auto&v:hi)v=random_f();std::array<F,3>abc;std::array<F,4>a;for(auto&v:abc)v=random_f();for(auto&v:a)v=random_f();if(c==0)a.fill(F());if(c==1)a.fill(F(1));if(c==2)abc.fill(F());
  SparseKernel k(abc,a);V w(1024),d;for(int j=0;j<1024;j++)w[j]=lo[j&15]*hi[j>>4];for(int j:support)d.push_back(w[t.p[j]]-w[j]);auto out=factored(lo,hi,k);assert(out==k.sparse_nested(support,d));correction++;if(c<24){assert(out==direct(support,d,abc,a));dense++;}
 }
 int shared=0,stages=0;bool negative=false;for(int c=0;c<96;c++){
  F rho=c==0?F():c==1?F(1):c==2?-F(1):random_f(),power=rho;V s(22),v0(22),v1(22),q0(256),q1(256);std::array<V,22>b;
  for(int i=0;i<22;i++){s[i]=power;power=power*rho;v0[i]=random_f();v1[i]=random_f();b[i]=line_basis(F(next_u()));}F l=s[21],inc;
  for(int ch=0;ch<2;ch++)for(int i=0;i<22;i++){F sc=ch?l*s[i]:s[i];inc=inc+sc*(ch?v1[i]:v0[i]);V&q=ch?q1:q0;for(int j=0;j<256;j++)q[j]=q[j]+sc*b[i][j];}
  assert(inc==dot(s,v0)+l*dot(s,v1));for(int r=0;r<=3;r++){for(size_t j=0;j<q0.size();j++)assert(q1[j]==l*q0[j]);stages++;if(r<3){F a=c<3?rho:random_f();q0=dfold(q0,a);q1=dfold(q1,a);}}
  V f0(4),f1(4),both(4);for(int j=0;j<4;j++){f0[j]=random_f();f1[j]=random_f();both[j]=f0[j]+l*f1[j];}assert(dot(q0,f0)+dot(q1,f1)==dot(q0,both));if(c>3&&dot(q0,f0)+dot(q1,f1)!=dot(q0,f0)+dot(q0,f1))negative=true;shared++;
 }assert(negative);
 int opening=0;bool negsplit=false;for(int c=0;c<1024;c++){
  F x=random_f(),y=random_f(),a=random_f();if(x==F()||y==F()){c--;continue;}Four all,g,rq,gq,tq;F r0=random_f(),r1=random_f(),g0=random_f(),g1=random_f();
  for(int j=0;j<4;j++){all[j]=random_f();g[j]=random_f();F h=j<2?x:-x,d=random_f();if(d==F())d=F(1);F inv=d.inv();rq[j]=(all[j]-g[j]-r0-r1*h)*inv;gq[j]=(g[j]-g0-g1*h)*inv;tq[j]=(all[j]-(r0+g0)-(r1+g1)*h)*inv;assert(rq[j]+gq[j]==tq[j]);}
  assert(fold4(x,y,a,rq)+fold4(x,y,a,gq)==fold4(x,y,a,tq));gq[0]=gq[0]+F(1);if(fold4(x,y,a,rq)+fold4(x,y,a,gq)!=fold4(x,y,a,tq))negsplit=true;opening++;
 }assert(negsplit);
 uint64_t arithmetic=0;U edge[]={0,1,2,3,P-3,P-2,P-1};for(U a:edge)for(U b:edge){assert(addfast(a,b)==(B(a)+B(b)).x);assert(subfast(a,b)==(B(a)-B(b)).x);assert(mulfast(a,b)==(B(a)*B(b)).x);assert(mulfast(a,b)==uint64_t(a)*b%P);arithmetic++;}
 for(int c=0;c<200000;c++){U a=next_u(),b=next_u();assert(addfast(a,b)==(B(a)+B(b)).x);assert(subfast(a,b)==(B(a)-B(b)).x);assert(mulfast(a,b)==(B(a)*B(b)).x);assert(mulfast(a,b)==uint64_t(a)*b%P);unsigned n=c%31;B v(a);for(unsigned j=0;j<n;j++)v=v.half();assert(halfn(a,n)==v.x);arithmetic++;}
 uint64_t generic=(uint64_t(1)<<62)-1;uint64_t folded=(generic&P)+(generic>>31);assert(folded==2*uint64_t(P));assert(folded-P==P);assert(generic%P==0);
 unsigned __int128 mx=4*(static_cast<unsigned __int128>(P-1)*(P-1));assert(mx<std::numeric_limits<uint64_t>::max());
 for(unsigned k=2;k<=7;k++){U p=(U(1)<<k)-1;for(U a=0;a<p;a++)for(U b=0;b<p;b++){uint64_t v=uint64_t(a)*b,s=(v&p)+(v>>k);assert(U(s>=p?s-p:s)==v%p);}}
 std::cout<<"{\"field\":\"QM31\",\"factored_correction_cases\":"<<correction<<",\"independent_chord_cases\":"<<dense<<",\"query_sharing_cases\":"<<shared<<",\"query_fold_stages\":"<<stages<<",\"opening_algebra_cases\":"<<opening<<",\"canonical_arithmetic_cases\":"<<arithmetic<<",\"negative_controls\":3,\"all_passed\":true,\"rust_compiled\":false,\"sbf_executed\":false}\n";
}
