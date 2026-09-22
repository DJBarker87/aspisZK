// R20 independent arithmetic implementations. Not extracted Rust or SBF.
#pragma once
#include "model.hpp"
#include <limits>
#include <stdexcept>
using Limbs=std::array<U,4>;
inline Limbs limbs(Q x){return {x.a.a.x,x.a.b.x,x.b.a.x,x.b.b.x};}
inline Q field(Limbs x){for(U a:x)assert(a<P);return Q(C(B(x[0]),B(x[1])),C(B(x[2]),B(x[3])));}
inline U mod64(uint64_t x){x=(x&P)+(x>>31);x=(x&P)+(x>>31);return U(x>=P?x-P:x);}
inline U canon_add(U a,U b){assert(a<P&&b<P);U s=a+b;return s>=P?s-P:s;}
inline U canon_sub(U a,U b){assert(a<P&&b<P);U s=a+P-b;return s>=P?s-P:s;}
inline U rotate31(U a,unsigned n){assert(a<P&&n<31);return n?((a>>n)|((a&((U(1)<<n)-1))<<(31-n))):a;}
constexpr uint64_t LANES=0x7fffffff7fffffffULL, ONES=0x0000000100000001ULL;
inline uint64_t pack2(U a,U b){assert(a<P&&b<P);return uint64_t(a)|(uint64_t(b)<<32);}
inline uint64_t lane_reduce(uint64_t s){return (s+(((s+ONES)>>31)&ONES))&LANES;}
inline uint64_t lane_add(uint64_t a,uint64_t b){return lane_reduce(a+b);}
inline uint64_t lane_sub(uint64_t a,uint64_t b){return lane_reduce(a+LANES-b);}
inline uint64_t lane_half(uint64_t a){return ((a>>1)&0x3fffffff3fffffffULL)|((a&ONES)<<30);}
inline bool canonical(Limbs x){for(U a:x)if(a>=P)return false;return true;}
// More products, fewer reductions/branches; must A/B against actual staged kernels.
inline Q schoolbook6(Q x,Q y){auto a=limbs(x),b=limbs(y);constexpr W PP=W(P)*P;
 W ar=a[0],ai=a[1],br=a[2],bi=a[3],cr=b[0],ci=b[1],dr=b[2],di=b[3];
 U u=mod64(br*dr+PP-bi*di),v=mod64(br*di+bi*dr);
 W r0=ar*cr+PP-ai*ci+2*W(u)+P-v;
 W i0=ar*ci+ai*cr+u+2*W(v);
 W r1=ar*dr+br*cr+2*PP-ai*di-bi*ci;
 W i1=ar*di+ai*dr+br*ci+bi*cr;
 return field({mod64(r0),mod64(i0),mod64(r1),mod64(i1)});
}
inline std::array<U,9> channels(Q x){auto a=limbs(x);U s0=canon_add(a[0],a[2]),s1=canon_add(a[1],a[3]);return {a[0],a[1],canon_add(a[0],a[1]),a[2],a[3],canon_add(a[2],a[3]),s0,s1,canon_add(s0,s1)};}
struct Dot9 {
 std::array<W,9> raw{},total{};unsigned pending=0,count=0;
 void flush(){for(int i=0;i<9;i++){total[i]+=(raw[i]&P)+(raw[i]>>31);raw[i]=0;}pending=0;}
 void push(Q x,Q y){assert(count<4096);if(pending==4)flush();auto a=channels(x),b=channels(y);for(int i=0;i<9;i++)raw[i]+=W(a[i])*b[i];count++;pending++;}
 Q finish(){if(count==0)return Q();const bool small=count<=4;if(!small&&pending)flush();std::array<B,9> r;for(int i=0;i<9;i++)r[i]=B(mod64(small?raw[i]:total[i]));auto part=[&](int i){return C(r[i]-r[i+1],r[i+2]-r[i]-r[i+1]);};C m0=part(0),m1=part(3),m2=part(6);return Q(m0+m1*C(B(2),B(1)),m2-m0-m1);}
};
inline Q dot_whole(const V&a,const V&b){assert(a.size()==b.size()&&a.size()<=4096);Dot9 d;for(size_t i=0;i<a.size();i++)d.push(a[i],b[i]);return d.finish();}
inline std::array<Q,27> zero_boundary(Q x){std::array<Q,27>b;b[0]=Q(1)-x-x;Q p=x*x;for(int i=1;i<27;i++){b[i]=p-x;if(i!=26)p=p*x;}return b;}
inline Q semantic_cached(Q claim,const std::array<Q,27>&sent,Q x,const std::array<Q,27>&b){Dot9 d;for(int i=0;i<27;i++)d.push(sent[i],b[i]);return claim*x+d.finish();}
inline Q semantic_reference(Q claim,const std::array<Q,27>&sent,Q x){std::array<Q,28>p{};p[0]=sent[0];Q sum=p[0]+p[0];for(int d=2;d<28;d++){p[d]=sent[d-1];sum=sum+p[d];}p[1]=claim-sum;Q r;for(int d=27;d>=0;d--)r=r*x+p[d];return r;}
// Transpose the grouped carry once, after contracting the final four-vector.
inline std::pair<std::array<Q,64>,std::array<Q,64>> scalar_high(const SparseKernel&k,Four final){std::array<Q,64>h{},c{};for(int j=0;j<64;j++)h[j]=k.h[j&15]*final[j>>4];for(int j=0;j<64;j++)for(auto e:edges(j))if(e.first<64)c[e.first]=c[e.first]+h[j]*e.second;return {h,c};}
inline Q sparse_scalar(const SparseKernel&k,Four final,std::array<Q,10>z){auto hc=scalar_high(k,final);auto coeff=[&](int i){int row=128+3*i,g=row>>4,l=row&15;Q v=k.n[l]*hc.first[g];if(l<3)v=v+k.c[l]*hc.second[g];return v;};Q total=coeff(0);for(int b=0;b<10;b++)total=total.half();
 for(int r=0;r<10;r++){int start=1+27*r;Q v0=coeff(start),sum,horner;std::array<Q,26>a;for(int j=0;j<26;j++){a[j]=coeff(start+1+j);sum=sum+a[j];}for(int j=25;j>=0;j--)horner=horner*z[r]+a[j];Q part=v0*(Q(1)-z[r]-z[r])+z[r]*(z[r]*horner-sum);for(int b=0;b<9-r;b++)part=part.half();total=total+part;}
 for(int b=0;b<8;b++){total=total.half();}return total;}
// Balanced convolution-like contraction: whole dot within each low group.
inline Four sparse_group_dots(const SparseKernel&k,const V&coins){assert(coins.size()==271);std::array<Dot9,64>n,c;for(int i=0;i<271;i++){int row=128+3*i,g=row>>4,l=row&15;n[g].push(coins[i],k.n[l]);if(l<3)c[g].push(coins[i],k.c[l]);}std::array<Q,64>ns,cs;for(int j=0;j<64;j++){ns[j]=n[j].finish();cs[j]=c[j].finish();}std::array<Dot9,4>out;for(int j=0;j<64;j++){Q v=ns[j];for(auto e:edges(j))if(e.first<64)v=v+cs[e.first]*e.second;out[j>>4].push(v,k.h[j&15]);}Four r;for(int j=0;j<4;j++){r[j]=out[j].finish();for(int b=0;b<8;b++)r[j]=r[j].half();}return r;}
inline Q basepack(const std::array<Q,4>&x){static const Q basis[4]={Q(1),Q(C(B(0),B(1)),C()),Q(C(),C(B(1),B(0))),Q(C(),C(B(0),B(1)))};Q r;for(int i=0;i<4;i++)r=r+x[i]*basis[i];return r;}
inline Q digestpack(const std::array<U,8>&d,int half){return field({d[4*half],d[4*half+1],d[4*half+2],d[4*half+3]});}
struct DigestEvent {int group;Q high;std::array<U,8> expected;};
using Opened=std::array<Q,16>;using Groups=std::array<std::array<Q,2>,3>;
inline Groups digest_reference(const Opened&o,const std::vector<DigestEvent>&events){Groups out{};for(auto&e:events){assert(e.group>=0&&e.group<3);int offset=e.group==0?8:0;for(int h=0;h<2;h++){std::array<Q,4>res;for(int j=0;j<4;j++)res[j]=o[offset+4*h+j]-Q(e.expected[4*h+j]);out[e.group][h]=out[e.group][h]+e.high*basepack(res);}}return out;}
inline Groups digest_factored(const Opened&o,const std::vector<DigestEvent>&events){std::array<Q,3>h{};std::array<std::array<Dot9,2>,3>d;for(auto&e:events){h[e.group]=h[e.group]+e.high;for(int j=0;j<2;j++)d[e.group][j].push(e.high,digestpack(e.expected,j));}Groups out{};for(int g=0;g<3;g++)for(int j=0;j<2;j++){int off=(g==0?8:0)+4*j;std::array<Q,4>x;for(int k=0;k<4;k++)x[k]=o[off+k];out[g][j]=h[g]*basepack(x)-d[g][j].finish();}return out;}
// Canonical packed source framing remains unchanged.
inline std::vector<uint8_t> pack31(const std::vector<U>&v){assert(v.size()%8==0);std::vector<uint8_t>b(v.size()*31/8);for(size_t i=0;i<v.size();i++){assert(v[i]<=P);for(int j=0;j<31;j++)if((v[i]>>j)&1)b[(31*i+j)/8]|=uint8_t(1U<<((31*i+j)%8));}return b;}
inline bool decode31(const std::vector<uint8_t>&b,size_t n,std::vector<U>&out){if(!n||n%8||b.size()!=n*31/8)return false;out.assign(n,0);bool invalid=false;for(size_t i=0;i<n;i++){U v=0;for(int j=0;j<31;j++)v|=U((b[(31*i+j)/8]>>((31*i+j)%8))&1)<<j;out[i]=v;invalid|=v==P;}return !invalid;}
inline bool gamma_original(const std::vector<uint8_t>&c1,const std::vector<uint8_t>&c2,const std::array<Q,29>&p,Q beta,Four&out){std::vector<U>a,b;if(!decode31(c1,104,a)||!decode31(c2,48,b))return false;for(int s=0;s<4;s++){Q all,g;for(int j=0;j<26;j++)all=all+p[j]*Q(a[26*s+j]);for(int h=0;h<3;h++){int off=4*(4*h+s);Q x=field({b[off],b[off+1],b[off+2],b[off+3]});all=all+p[26+h]*x;if(h==1)g=p[27]*x;}out[s]=(Q(1)-beta)*(all-g)+beta*g;}return true;}
inline std::array<Q,29> prepare_beta(const std::array<Q,29>&p,Q beta){std::array<Q,29>q;for(int j=0;j<29;j++)q[j]=p[j]*(j==27?beta:Q(1)-beta);return q;}
inline bool gamma_fused(const std::vector<uint8_t>&c1,const std::vector<uint8_t>&c2,const std::array<Q,29>&p,Four&out){std::vector<U>a,b;if(!decode31(c1,104,a)||!decode31(c2,48,b))return false;for(int s=0;s<4;s++){// Use field reference here; real adapter retains mixed-width C1 dots.
 Dot9 d;for(int j=0;j<26;j++)d.push(p[j],Q(a[26*s+j]));for(int h=0;h<3;h++){int off=4*(4*h+s);d.push(p[26+h],field({b[off],b[off+1],b[off+2],b[off+3]}));}out[s]=d.finish();}return true;}
