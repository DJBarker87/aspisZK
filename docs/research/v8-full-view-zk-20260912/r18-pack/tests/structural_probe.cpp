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
int main(int argc,char**argv){std::string selection=argc>1?argv[1]:"spread";int trials=argc>2?std::stoi(argv[2]):3;int reset=argc>3?std::stoi(argv[3]):true;
 assert(trials>0&&trials<=100&&reset>=0&&reset<=2);Transport t(reset);for(int j=0;j<1024;j++){V m(1024);m[j]=F(1);assert(t.inverse(t.forward(m))==m);}for(int j=0;j<89;j++){V m(1024);m[t.p[j]]=F(1);m[t.pivot]=-F(1);auto c=t.forward(m);for(int k=0;k<1024;k++)assert(c[k]==F(k==j));}
 std::cout<<"{\"selection\":\""<<selection<<"\",\"reset_transport\":"<<reset<<",\"inverse_basis\":1024,\"legal_balanced_basis\":89,\"ranks\":[";
 for(int s=1;s<=trials;s++){auto a=selection=="h1"?build_h1(reset,s):build(reset,selection,s,true);int r=rank(a);if(s>1)std::cout<<",";std::cout<<r<<std::flush;}
 std::cout<<"],\"target\":"<<(selection=="h1"?540:601)<<",\"sampler_generated\":false,\"is_source_extraction\":false}\n";
 return 0;
}
