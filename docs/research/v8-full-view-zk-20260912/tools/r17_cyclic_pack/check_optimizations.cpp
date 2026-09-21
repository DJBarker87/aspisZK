// Independent exact-arithmetic checker. Not compiled Aspis Rust and not a CU benchmark.
// g++ -std=c++17 -O2 -Wall -Wextra -Werror check_optimizations.cpp -o check && ./check
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using U=uint32_t; using W=uint64_t;
constexpr U P=2147483647;
U add(U a,U b){W x=W(a)+b; return U(x>=P?x-P:x);}
U neg(U a){return a?P-a:0;}
U sub(U a,U b){return add(a,neg(b));}
U mul(U a,U b){W x=W(a)*b; x=(x&P)+(x>>31); return U(x>=P?x-P:x);}
U half(U a){return (a>>1)+((a&1)?1073741824U:0);}
U power(U a,W n){U r=1;for(;n;n>>=1,a=mul(a,a))if(n&1)r=mul(r,a);return r;}
struct C {
 U a=0,b=0;
 C()=default; C(U x,U y=0):a(x),b(y){}
 C operator+(C z)const{return {add(a,z.a),add(b,z.b)};}
 C operator-(C z)const{return {sub(a,z.a),sub(b,z.b)};}
 C operator*(C z)const{return {sub(mul(a,z.a),mul(b,z.b)),add(mul(a,z.b),mul(b,z.a))};}
 C scale(U n)const{return {mul(a,n),mul(b,n)};}
 C halve()const{return {half(a),half(b)};}
 bool operator==(C z)const{return a==z.a&&b==z.b;}
 bool operator!=(C z)const{return !(*this==z);}
 C pow(W n)const{C r(1),x=*this;for(;n;n>>=1,x=x*x)if(n&1)r=r*x;return r;}
 C inv()const{U norm=add(mul(a,a),mul(b,b));if(!norm)throw std::runtime_error("inverse of zero");U d=power(norm,P-2);return {mul(a,d),mul(neg(b),d)};}
};
void fft(std::vector<C>&a,bool inverse,C root){
 size_t n=a.size(); assert(n && !(n&(n-1)));
 for(size_t i=1,j=0;i<n;++i){size_t bit=n>>1;while(j&bit){j^=bit;bit>>=1;}j^=bit;if(i<j)std::swap(a[i],a[j]);}
 if(inverse)root=root.inv();
 for(size_t len=2;len<=n;len*=2){C step=root.pow(n/len);for(size_t base=0;base<n;base+=len){C w(1);for(size_t j=0;j<len/2;++j){C u=a[base+j],v=a[base+j+len/2]*w;a[base+j]=u+v;a[base+j+len/2]=u-v;w=w*step;}}}
 if(inverse){U d=power(U(n),P-2);for(C &x:a)x=x.scale(d);}
}
using Poly=std::vector<U>;
std::array<Poly,1024> den;
std::array<U,271> scale_coin,dc_weight;
std::vector<C> cyclic_inverse(1024),old_spectrum(2048);
C root2048,root1024;
std::vector<C> numerator(const std::vector<C>&coins){
 assert(coins.size()==271); auto current=coins; std::vector<C> next(271);
 for(size_t size=2;size<=512;size*=2){
  std::fill(next.begin(),next.end(),C());
  for(size_t start=0;start<271;start+=size){size_t mid=std::min(start+size/2,size_t(271)),end=std::min(start+size,size_t(271));
   if(mid==end){std::copy(current.begin()+start,current.begin()+end,next.begin()+start);continue;}
   size_t node=512/size+start/size;
   for(auto side: {std::array<size_t,3>{start,mid,node*2+1},std::array<size_t,3>{mid,end,node*2}}){
    for(size_t i=side[0];i<side[1];++i)for(size_t k=0;k<den[side[2]].size();++k){size_t at=start+i-side[0]+k;assert(at<end);next[at]=next[at]+current[i].scale(den[side[2]][k]);}
   }
  }
  current.swap(next);
 }
 return current;
}
void setup(){
 root2048=C(2,1268011823).pow(1<<20);root1024=root2048*root2048;
 assert(root2048.pow(2048)==C(1)&&root2048.pow(1024)!=C(1));
 assert(root1024.pow(1024)==C(1)&&root1024.pow(512)!=C(1));
 for(size_t i=0;i<512;++i)den[512+i]=i<271?Poly{1,neg(U(i+1))}:Poly{1};
 for(size_t i=511;i;--i){den[i].assign(den[i*2].size()+den[i*2+1].size()-1,0);for(size_t j=0;j<den[i*2].size();++j)for(size_t k=0;k<den[i*2+1].size();++k)den[i][j+k]=add(den[i][j+k],mul(den[i*2][j],den[i*2+1][k]));}
 std::vector<U> inverse(1024);inverse[0]=1;
 for(size_t j=1;j<1024;++j){U s=0;for(size_t k=1;k<=std::min(j,size_t(271));++k)s=add(s,mul(den[1][k],inverse[j-k]));inverse[j]=neg(s);}
 for(size_t j=0;j<1024;++j){old_spectrum[j]=C(inverse[j]);}
 fft(old_spectrum,false,root2048);
 std::vector<C> d(1024);for(size_t j=0;j<den[1].size();++j)d[j]=C(den[1][j]);fft(d,false,root1024);
 assert(d[0]==C()); // Node 1 creates the only exceptional Fourier coordinate.
 for(size_t k=1;k<1024;++k){assert(d[k]!=C());cyclic_inverse[k]=d[k].inv();assert(d[k]*cyclic_inverse[k]==C(1));}
 for(size_t i=0;i<271;++i){U a=U(i+1);scale_coin[i]=sub(1,power(a,1024));
  if(i==0){assert(scale_coin[i]==0);dc_weight[i]=1024;}
  else {assert(scale_coin[i]!=0);dc_weight[i]=mul(scale_coin[i],power(sub(1,a),P-2));U s=0,q=1;for(size_t j=0;j<1024;++j){s=add(s,q);q=mul(q,a);}assert(s==dc_weight[i]);}
 }
}
std::vector<C> direct(const std::vector<C>&coins){std::vector<C>r(1024);for(size_t i=0;i<271;++i){U q=1;for(size_t j=0;j<1024;++j){r[j]=r[j]+coins[i].scale(q);q=mul(q,U(i+1));}}return r;}
std::vector<C> old2048(const std::vector<C>&coins){auto n=numerator(coins);n.resize(2048);fft(n,false,root2048);for(size_t j=0;j<2048;++j)n[j]=n[j]*old_spectrum[j];fft(n,true,root2048);n.resize(1024);return n;}
std::vector<C> new1024(const std::vector<C>&coins,bool erase_dc=false){
 std::vector<C> scaled(271);C dc;
 for(size_t i=0;i<271;++i){scaled[i]=coins[i].scale(scale_coin[i]);dc=dc+coins[i].scale(dc_weight[i]);}
 auto n=numerator(scaled);n.resize(1024);fft(n,false,root1024);
 n[0]=erase_dc?C():dc;
 for(size_t j=1;j<1024;++j)n[j]=n[j]*cyclic_inverse[j];
 fft(n,true,root1024);return n;
}
// Incorrect tempting shortcut: wrap the old linear convolution modulo X^1024-1.
std::vector<C> naive1024(const std::vector<C>&coins){auto n=numerator(coins);n.resize(1024);fft(n,false,root1024);for(size_t k=0;k<1024;++k)n[k]=n[k]*old_spectrum[2*k];fft(n,true,root1024);return n;}
W seed=0x51413217a681fbadULL;
U random_scalar(){seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;return U(seed%P);}
C random_c(){return {random_scalar(),random_scalar()};}
C carry_old(const std::vector<C>&v,size_t j){size_t row=j,bit=0;U scale=1;C s;while(row&(size_t(1)<<bit)){row^=size_t(1)<<bit;scale=mul(scale,1073741824);s=s+v.at(row).scale(scale);++bit;}return s+v.at(row|(size_t(1)<<bit)).scale(scale);}
C carry_new(const std::vector<C>&v,size_t j){size_t t=0;while((j>>t)&1)++t;C s=v.at(j+1);while(t){--t;size_t r=j&~((size_t(1)<<(t+1))-1);s=(s+v.at(r)).halve();}return s;}
// The weighted-group zero extension is material: j=63 has a final edge to 64.
C group_old(const std::vector<C>&v,size_t j){std::vector<C>x=v;x.push_back(C());return carry_old(x,j);}
C group_new(const std::vector<C>&v,size_t j){std::vector<C>x=v;x.push_back(C());return carry_new(x,j);}
std::array<C,4> contract_old(const std::vector<C>&normal,const std::vector<C>&carry,const std::array<C,16>&high){std::array<C,4>out{};for(size_t j=0;j<64;++j)out[j>>4]=out[j>>4]+(normal[j]+group_old(carry,j))*high[j&15];for(auto &x:out)for(int i=0;i<8;++i)x=x.halve();return out;}
std::array<C,4> contract_new(const std::vector<C>&normal,const std::vector<C>&carry,const std::array<C,16>&high){std::array<C,4>out{};for(size_t j=0;j<64;++j)out[j>>4]=out[j>>4]+(normal[j]+group_new(carry,j))*high[j&15];for(auto &x:out)for(int i=0;i<8;++i)x=x.halve();return out;}
int main(){
 setup();size_t basis=0,dense=0,carry_cases=0,group_cases=0;
 for(size_t i=0;i<271;++i)for(int lane=0;lane<2;++lane){std::vector<C>c(271);c[i]=lane?C(0,1):C(1,0);auto got=new1024(c);U q=1;for(size_t j=0;j<1024;++j){assert(got[j]==c[i].scale(q));q=mul(q,U(i+1));}++basis;}
 // 32 full QM31 input vectors = 64 separately interpreted CM31 components.
 for(size_t case_no=0;case_no<32;++case_no)for(int component=0;component<2;++component){std::vector<C>c(271);for(size_t i=0;i<271;++i)c[i]=case_no==0?C():case_no==1?C(P-1,P-1):case_no==2?C(1,component):random_c();auto reference=direct(c);assert(old2048(c)==reference);assert(new1024(c)==reference);++dense;}
 {std::vector<C>c(271);c[0]=C(3,5);assert(new1024(c,true)!=direct(c));}
 {std::vector<C>c(271);c[270]=C(7,11);assert(naive1024(c)!=direct(c));}
 for(size_t case_no=0;case_no<80;++case_no){std::vector<C>v(1026);for(auto &x:v)x=case_no==0?C():case_no==1?C(P-1,P-1):random_c();for(size_t j=0;j<1025;++j){assert(carry_new(v,j)==carry_old(v,j));++carry_cases;}}
 for(size_t case_no=0;case_no<80;++case_no){std::vector<C>n(64),c(64);std::array<C,16>h{};for(auto &x:h)x=random_c();for(auto &x:n)x=random_c();for(auto &x:c)x=random_c();assert(contract_new(n,c,h)==contract_old(n,c,h));++group_cases;
  // Pivot 1023: local coordinate 15 => no carry; only terminal coordinate 3.
  std::fill(n.begin(),n.end(),C());std::fill(c.begin(),c.end(),C());C p=random_c();n[63]=p;auto r=contract_new(n,c,h);C expected=p*h[15];for(int k=0;k<8;++k)expected=expected.halve();assert(r[0]==C()&&r[1]==C()&&r[2]==C()&&r[3]==expected);
 }
 size_t trailing_sum=0;for(size_t n: {size_t(513),size_t(512),size_t(512)})for(size_t j=0;j<n;++j){size_t v=j;while(v&1){++trailing_sum;v>>=1;}}
 std::cout<<"{\n  \"cyclic_basis_cm31\": "<<basis<<",\n  \"dense_cm31_three_way_comparisons\": "<<dense<<",\n  \"dense_qm31_vectors\": 32,\n  \"cyclic_zero_denominators\": 1,\n  \"cyclic_nonzero_denominators_checked\": 1023,\n  \"negative_controls\": 2,\n  \"carry_kernel_comparisons\": "<<carry_cases<<",\n  \"weighted_group_comparisons\": "<<group_cases<<",\n  \"pivot_shortcuts\": 80,\n  \"old_fft_butterflies_two_components\": 45056,\n  \"new_fft_butterflies_two_components\": 20480,\n  \"old_chord_carry_m31_multiplies_per_channel\": "<<4*(1537+trailing_sum)+trailing_sum<<",\n  \"new_chord_carry_qm31_halves_per_channel\": "<<trailing_sum<<",\n  \"all_passed\": true,\n  \"is_solana_cu_measurement\": false\n}\n";
}
