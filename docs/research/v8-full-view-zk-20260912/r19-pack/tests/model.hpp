// Retained independent R18 model, NOT extracted Rust.
// Exact finite-field SOURCE-SHAPED probe, not extracted Rust, SBF or a privacy theorem.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
#ifdef NDEBUG
#error "Assertions are mandatory for this verification probe"
#endif
using U=uint32_t; using W=uint64_t;
constexpr U P=2147483647, HALF=1073741824;
struct B {
 U x=0; B()=default; B(U a):x(a%P){}
 static B raw(U x){B a;a.x=x;return a;}
 B operator+(B b)const{W s=W(x)+b.x;return raw(U(s>=P?s-P:s));}
 B operator-(B b)const{return raw(x>=b.x?x-b.x:P-(b.x-x));}
 B operator*(B b)const{W a=W(x)*b.x;a=(a&P)+(a>>31);return raw(U(a>=P?a-P:a));}
 B operator-()const{return raw(x?P-x:0);}
 bool operator==(B b)const{return x==b.x;} bool operator!=(B b)const{return x!=b.x;}
 B pow(W n)const{B a=*this,r(1);for(;n;n>>=1,a=a*a)if(n&1)r=r*a;return r;}
 B inv()const{assert(x);return pow(P-2);}
 B half()const{return raw((x>>1)+((x&1)?HALF:0));}
};

struct C {
 B a{},b{};C()=default;C(U x):a(x){};C(B x,B y):a(x),b(y){}
 C operator+(C z)const{return {a+z.a,b+z.b};}C operator-(C z)const{return {a-z.a,b-z.b};}
 C operator-()const{return {-a,-b};}C operator*(C z)const{return {a*z.a-b*z.b,a*z.b+b*z.a};}
 C half()const{return {a.half(),b.half()};}bool operator==(C z)const{return a==z.a&&b==z.b;}
 C inv()const{B n=(a*a+b*b).inv();return {a*n,-b*n};}
};
struct Q {
 C a{},b{};Q()=default;Q(U x):a(x){};Q(C x,C y):a(x),b(y){}
 Q operator+(Q z)const{return {a+z.a,b+z.b};}Q operator-(Q z)const{return {a-z.a,b-z.b};}
 Q operator-()const{return {-a,-b};}Q operator*(Q z)const{return {a*z.a+(b*z.b)*C(B(2),B(1)),a*z.b+b*z.a};}
 Q half()const{return {a.half(),b.half()};}bool operator==(Q z)const{return a==z.a&&b==z.b;}bool operator!=(Q z)const{return !(*this==z);}
 Q pow(W n)const{Q a=*this,r(1);for(;n;n>>=1,a=a*a)if(n&1)r=r*a;return r;}
 Q inv()const{C n=(a*a-(b*b)*C(B(2),B(1))).inv();return {a*n,-b*n};}
};
#ifdef EXTENSION
using F=Q;
F parameter(U n){return Q(C(B(n+1),B(3*n+7)),C(B(5*n+11),B(7*n+13)));}
#else
using F=B;
F parameter(U n){return F(n);}
#endif
using V=std::vector<F>; using Mat=std::vector<V>;
static const U MASKS[64]={6144,6144,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6144,4097,2048,6145,2049,2048,6145,2049,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,4097,6145,6145,4097,26214,26214,26214,26214,26214,26214,1749};
bool inactive(int r){return !(MASKS[r/16]&(1U<<(r%16)));}
// The selected candidates use ONLY last rows (15) and Poseidon padding rows.
// Last row of value block is the old source-asserted legal pivot 1023.
bool candidate_legal(int r){return inactive(r)&&((r<912&&r%16>=13)||(r>=912&&r<1008&&r%16==15)||r==1023);}
int affine_order(int j){return 16*(j&63)+(15-(j>>6));}
struct Transport{
 std::array<int,1024> p{};int pivot=1023;
 explicit Transport(int reset){
  if(reset==1){for(int j=0;j<1024;j++)p[j]=affine_order(j);std::swap(p[128],p[1023]);pivot=13;}
  else {std::vector<int> pads;for(int r=0;r<912&&pads.size()<89;r++)if(candidate_legal(r)&&r!=1014)pads.push_back(r);
   assert(pads.size()==89);
   if(reset==2){std::iota(p.begin(),p.end(),0);for(int j=0;j<89;j++)p[j]=pads[j];std::vector<int>missing,holes;for(int j=0;j<89;j++)if(std::find(pads.begin(),pads.end(),j)==pads.end())missing.push_back(j);for(int r:pads)if(r>=89)holes.push_back(r);assert(missing.size()==holes.size());for(size_t i=0;i<holes.size();i++)p[holes[i]]=missing[i];}
   else {int j=0;for(int r:pads)p[j++]=r;for(int r=0;r<1023;r++)if(std::find(pads.begin(),pads.end(),r)==pads.end())p[j++]=r;p[j]=1023;}}
  auto q=p;std::sort(q.begin(),q.end());for(int j=0;j<1024;j++)assert(q[j]==j);
  assert(p[1023]==pivot&&inactive(pivot));for(int j=0;j<89;j++)assert(candidate_legal(p[j]));
 }
 V forward(const V&m)const{V c(1024);for(int j=0;j<1024;j++)c[j]=m[p[j]];c[1023]=F();for(int r=0;r<1024;r++)if(inactive(r))c[1023]=c[1023]+m[r];return c;}
 V inverse(const V&c)const{V m(1024);for(int j=0;j<1024;j++)m[p[j]]=c[j];F s;for(int r=0;r<1024;r++)if(r!=pivot&&inactive(r))s=s+m[r];m[pivot]=c[1023]-s;return m;}
 V dual(const V&w)const{V d(1024);for(int j=0;j<1024;j++){int r=p[j];d[j]=w[r];if(r!=pivot&&inactive(r))d[j]=d[j]-w[pivot];}return d;}
};
F dot(const V&a,const V&b){assert(a.size()==b.size());F s;for(size_t j=0;j<a.size();j++)s=s+a[j]*b[j];return s;}
V tx(const V&v){V o(v.size()+1);for(size_t j=0;j<v.size();j++){size_t r=j,k=0;F s(1);while(r&(size_t(1)<<k)){r^=size_t(1)<<k;s=s.half();o[r]=o[r]+v[j]*s;k++;}o[r|(size_t(1)<<k)]=o[r|(size_t(1)<<k)]+v[j]*s;}return o;}
V chord_full(const V&q,std::array<F,3>abc){V e(512),o(512);for(int j=0;j<512;j++){e[j]=q[2*j];o[j]=q[2*j+1];}auto xe=tx(e),xo=tx(o),xxo=tx(xo);V c(1028);auto get=[](const V&v,int j){return j<int(v.size())?v[j]:F();};for(int j=0;j<514;j++){c[2*j]=abc[0]*get(e,j)+abc[1]*get(xe,j)+abc[2]*(get(o,j)-get(xxo,j));c[2*j+1]=abc[2]*get(e,j)+abc[0]*get(o,j)+abc[1]*get(xo,j);}return c;}
std::array<F,2> circle(F t){F d=(F(1)+t*t).inv();return {(F(1)-t*t)*d,F(2)*t*d};}
V evalbasis(std::array<F,2>pt){std::array<F,10>f{};f[0]=pt[1];f[1]=pt[0];for(int i=2;i<10;i++)f[i]=F(2)*f[i-1]*f[i-1]-F(1);V v(1024,F(1));for(int j=0;j<1024;j++)for(int b=0;b<10;b++)if(j&(1<<b))v[j]=v[j]*f[b];return v;}
V mle(std::array<F,10>z){V v(1024,F(1));for(int j=0;j<1024;j++)for(int b=0;b<10;b++)v[j]=v[j]*((j>>(9-b)&1)?z[b]:F(1)-z[b]);return v;}
std::array<std::array<F,10>,3> statement(std::array<F,10>z){auto a=z,b=z;F carry(1);for(int j=9;j>=0;j--){a[j]=z[j]+carry-F(2)*z[j]*carry;carry=carry*z[j];}b[7]=F(1)-b[7];b[6]=F(1)-b[6];return {z,a,b};}
V coinweights(std::array<F,10>z){V a(271);F scale(1);for(int r=9;r>=0;r--){int k=1+27*r;a[k]=scale*(F(1)-F(2)*z[r]);F power=z[r]*z[r];for(int i=1;i<27;i++){a[k+i]=scale*(power-z[r]);power=power*z[r];}scale=scale.half();}a[0]=scale;return a;}
std::vector<int> slots(std::string name){std::vector<int>s;
 if(name=="first271")for(int i=0;i<271;i++)s.push_back(i);
 if(name=="stride3")for(int i=0;i<271;i++)s.push_back(128+3*i);
 if(name=="lane3") {for(int j=32;j<255;j++)s.push_back(4*j+3);for(int j=32;j<80;j++)s.push_back(4*j+2);}
 if(name=="spread") {for(int j=32;j<255;j++)s.push_back(4*j+3);for(int j=0;j<48;j++)s.push_back(4*(32+(j*37)%223)+2);}
 assert(s.size()==271);auto t=s;std::sort(t.begin(),t.end());assert(std::adjacent_find(t.begin(),t.end())==t.end()&&t.back()<1023);return s;}
// Row-echelon rank; original matrix is separately retained for image certificates later.
int rank(Mat a){int r=0,n=a.size(),m=a[0].size();for(int j=0;j<m&&r<n;j++){int p=r;while(p<n&&a[p][j]==F())p++;if(p==n)continue;std::swap(a[r],a[p]);F inv=a[r][j].inv();for(int k=j;k<m;k++)a[r][k]=a[r][k]*inv;for(int i=r+1;i<n;i++)if(a[i][j]!=F()){F f=a[i][j];for(int k=j;k<m;k++)a[i][k]=a[i][k]-f*a[r][k];}r++;}return r;}
Mat build(int reset,std::string selection,int seed,bool relation){
 Transport t(reset);auto S=slots(selection);std::array<F,10>z;for(int i=0;i<10;i++)z[i]=parameter(seed*67+i*11+3);
 auto pts=statement(z);auto cw=coinweights(z);F k=parameter(seed*29+7),tau=parameter(seed*31+11),alpha=parameter(seed*13+19);auto p0=circle(parameter(seed*31+2)),p1=circle(parameter(seed*37+17));std::array<F,3>abc={p0[0]*p1[1]-p0[1]*p1[0],p0[1]-p1[1],p1[0]-p0[0]};
 std::vector<V>raw;V roots;for(int i=0;i<22;i++){auto pt=circle(F(seed*101+1000+7919*i));assert(pt[0]!=F()&&pt[1]!=F());F root=F(2)*pt[0]*pt[0]-F(1);assert(std::find(roots.begin(),roots.end(),root)==roots.end());roots.push_back(root);for(int b=0;b<4;b++){auto x=b<2?pt[0]:-pt[0],y=(b==0||b==3)?pt[1]:-pt[1];assert(abc[0]+abc[1]*x+abc[2]*y!=F());raw.push_back(evalbasis({x,y}));}}
 auto w1=t.dual(mle(pts[1])),w2=t.dual(mle(pts[2]));V wg(1024);for(int i=0;i<271;i++)wg[S[i]]=cw[i]*k;for(int j=0;j<1024;j++)wg[j]=wg[j]+k*k*w1[j]+k*k*k*w2[j];wg[1023]=wg[1023]+F(1);
 V lweights(1024);for(int j=0;j<1024;j++){V q(1024);q[j]=F(1);auto c=chord_full(q,abc);c.resize(1024);lweights[j]=dot(c,wg);}lweights[1023]=lweights[1023]+tau.pow(3);lweights[1022]=lweights[1022]+tau.pow(4)*abc[1];lweights[1021]=lweights[1021]-tau.pow(4)*abc[2];
 // Eliminate sparse final/coin/balance equations first, then dense raw/point/relation.
 Mat a(256+271+1+88+2+(relation?6:0),V(1022));
 for(int j=0;j<1022;j++){V q(1024);if(j<1021)q[j]=F(1);else {q[1021]=abc[1];q[1022]=abc[2];}auto c=chord_full(q,abc);for(int h=1024;h<1028;h++)assert(c[h]==F());c.resize(1024);
  for(int b=0;b<256;b++)a[b][j]=q[4*b]+alpha*(q[4*b+1]+alpha*(q[4*b+2]+alpha*q[4*b+3]));
  for(int i=0;i<271;i++){a[256+i][j]=c[S[i]];}a[527][j]=c[1023];
  for(int i=0;i<88;i++){a[528+i][j]=dot(c,raw[i]);}a[616][j]=dot(c,w1);a[617][j]=dot(c,w2);
  if(relation){std::array<F,7>p{};int order[4]={0,3,2,1};for(int b=0;b<256;b++)for(int i=0;i<4;i++)for(int h=0;h<4;h++)p[i+h]=p[i+h]+(q[4*b+i]*lweights[4*b+order[h]]).half().half();int sent[6]={0,1,2,3,5,6};for(int i=0;i<6;i++)a[618+i][j]=p[sent[i]];
   F boundary=F(4)*(p[0]+p[4]);assert(boundary==dot(q,lweights));
  }
 }
 return a;
}

Mat build_h1(int reset,int seed){
 Transport t(reset);std::array<F,10>z;for(int i=0;i<10;i++)z[i]=parameter(seed*67+i*11+3);
 auto pts=statement(z);F alpha=parameter(seed*13+19);auto p0=circle(parameter(seed*31+2)),p1=circle(parameter(seed*37+17));std::array<F,3>abc={p0[0]*p1[1]-p0[1]*p1[0],p0[1]-p1[1],p1[0]-p0[0]};
 std::vector<int>active;for(int r=0;r<1024;r++)if(!inactive(r))active.push_back(r);assert(active.size()==214);
 std::vector<V>raw;V roots;for(int i=0;i<22;i++){auto pt=circle(F(seed*101+1000+7919*i));assert(pt[0]!=F()&&pt[1]!=F());F root=F(2)*pt[0]*pt[0]-F(1);assert(std::find(roots.begin(),roots.end(),root)==roots.end());roots.push_back(root);for(int b=0;b<4;b++){auto x=b<2?pt[0]:-pt[0],y=(b==0||b==3)?pt[1]:-pt[1];assert(abc[0]+abc[1]*x+abc[2]*y!=F());raw.push_back(evalbasis({x,y}));}}
 std::array<V,3>wp={t.dual(mle(pts[0])),t.dual(mle(pts[1])),t.dual(mle(pts[2]))};Mat a(562,V(1022));
 for(int j=0;j<1022;j++){V q(1024);if(j<1021)q[j]=F(1);else{q[1021]=abc[1];q[1022]=abc[2];}auto c=chord_full(q,abc);for(int h=1024;h<1028;h++)assert(c[h]==F());c.resize(1024);auto m=t.inverse(c);
  for(int i=0;i<214;i++){a[i][j]=m[active[i]];}a[214][j]=c[1023];
  for(int i=0;i<256;i++)a[215+i][j]=q[4*i]+alpha*(q[4*i+1]+alpha*(q[4*i+2]+alpha*q[4*i+3]));
  for(int i=0;i<88;i++){a[471+i][j]=dot(c,raw[i]);}for(int i=0;i<3;i++){a[559+i][j]=dot(c,wp[i]);}
 }
 return a;
}
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
