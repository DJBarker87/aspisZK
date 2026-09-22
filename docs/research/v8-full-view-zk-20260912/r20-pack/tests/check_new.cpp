#include "new_kernels.hpp"
uint64_t seed=0x69f19350b3a18765ULL;
U random_u(){seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;return U(seed%P);}
Q random_q(){return field({random_u(),random_u(),random_u(),random_u()});}
int main(){
 unsigned long long packed_cases=0,product_cases=0,dot_cases=0,semantic_cases=0,sparse_cases=0,digest_cases=0,gamma_cases=0,rejections=0;
 const U edges_[]={0,1,2,3,P/2,P-3,P-2,P-1};
 for(int i=0;i<200000;i++){
  U a=random_u(),b=random_u(),c=random_u(),d=random_u();if(i<4096){int k=i;a=edges_[k%8];k/=8;b=edges_[k%8];k/=8;c=edges_[k%8];k/=8;d=edges_[k%8];}
  W x=pack2(a,b),y=pack2(c,d);W plus=lane_add(x,y),minus=lane_sub(x,y),half=lane_half(x);
  assert(plus==pack2((B(a)+B(c)).x,(B(b)+B(d)).x));assert(minus==pack2((B(a)-B(c)).x,(B(b)-B(d)).x));assert(half==pack2(B(a).half().x,B(b).half().x));
  Q u=random_q(),v=random_q();if(i<256){auto pick=[&](int k){return ((i>>k)&1)?P-1:0;};u=field({pick(0),pick(1),pick(2),pick(3)});v=field({pick(4),pick(5),pick(6),pick(7)});}
  assert(schoolbook6(u,v)==u*v);packed_cases++;product_cases++;
  unsigned n=i%31;B ref(a);for(unsigned j=0;j<n;j++)ref=ref.half();assert(rotate31(a,n)==ref.x);
 }
 // Exhaust analogous two-lane add/sub schemes at reduced widths, including zero.
 unsigned long long reduced=0;for(unsigned width=2;width<=4;width++){U p=(1U<<width)-1;W one=1ULL|(1ULL<<(width+1)),mask=p|(W(p)<<(width+1));auto red=[&](W s){return (s+(((s+one)>>width)&one))&mask;};for(U a=0;a<p;a++)for(U b=0;b<p;b++)for(U c=0;c<p;c++)for(U d=0;d<p;d++){W x=a|(W(b)<<(width+1)),y=c|(W(d)<<(width+1));assert(red(x+y)==(W((a+c)%p)|(W((b+d)%p)<<(width+1))));W want=W((a+p-c)%p)|(W((b+p-d)%p)<<(width+1));assert(red(x+mask-y)==want);reduced++;}}
 for(int n:{0,1,2,3,4,5,7,8,16,26,27,28,64,89,163,271,1024,4096})for(int c=0;c<16;c++){V a(n),b(n);for(int j=0;j<n;j++){a[j]=random_q();b[j]=random_q();if(c==0)a[j]=Q();if(c==1)a[j]=b[j]=field({P-1,P-1,P-1,P-1});}assert(dot_whole(a,b)==dot(a,b));dot_cases++;}
 for(int c=0;c<256;c++){Q claim=random_q();std::array<Q,10>z;std::array<std::array<Q,27>,10>cache;for(int r=0;r<10;r++){z[r]=c<3?Q(c):random_q();std::array<Q,27>s;for(auto&x:s)x=random_q();cache[r]=zero_boundary(z[r]);Q next=semantic_cached(claim,s,z[r],cache[r]);assert(next==semantic_reference(claim,s,z[r]));claim=next;semantic_cases++;}auto source=coinweights(z);for(int r=0;r<10;r++)for(int i=0;i<27;i++){Q v=cache[r][i];for(int b=0;b<9-r;b++)v=v.half();assert(v==source[1+27*r+i]);}}
 for(int c=0;c<96;c++){std::array<Q,10>z;std::array<Q,3>abc;std::array<Q,4>a;Four finals;for(auto&v:z)v=c==0?Q():c==1?Q(1):random_q();for(auto&v:abc)v=c==2?Q():random_q();for(auto&v:a)v=c==3?Q():c==4?Q(1):random_q();for(auto&v:finals)v=random_q();SparseKernel k(abc,a);auto coins=coinweights(z);auto old=k.sparse_nested(slots("stride3"),coins);auto fused=sparse_group_dots(k,coins);assert(fused==old);assert(sparse_scalar(k,finals,z)==dot(V(old.begin(),old.end()),V(finals.begin(),finals.end())));if(c<12){assert(old==direct(slots("stride3"),coins,abc,a));}sparse_cases++;}
 for(int c=0;c<2048;c++){Opened o;for(auto&v:o)v=random_q();std::vector<DigestEvent>events;for(int j=0;j<(c%27);j++){DigestEvent e;e.group=j%3;e.high=random_q();for(auto&v:e.expected)v=random_u();if(c%13==0)e.high=Q();events.push_back(e);}assert(digest_factored(o,events)==digest_reference(o,events));digest_cases++;}
 for(int c=0;c<256;c++){std::vector<U>a(104),b(48);for(auto&v:a)v=c==0?0:c==1?P-1:random_u();for(auto&v:b)v=c==0?0:c==1?P-1:random_u();auto ab=pack31(a),bb=pack31(b);std::array<Q,29>p;Q gamma=random_q();p[0]=Q(1);for(int j=1;j<29;j++)p[j]=p[j-1]*gamma;if(c%11==0)for(auto&v:p)v=random_q();for(Q beta:{Q(),Q(1),-Q(1),random_q()}){Four old,now;assert(gamma_original(ab,bb,p,beta,old));assert(gamma_fused(ab,bb,prepare_beta(p,beta),now));assert(old==now);gamma_cases++;}}
 for(int bad=0;bad<152;bad++)for(Q beta:{Q(),Q(1),random_q()}){std::vector<U>v(152);v[bad]=P;auto a=pack31(std::vector<U>(v.begin(),v.begin()+104)),b=pack31(std::vector<U>(v.begin()+104,v.end()));std::array<Q,29>p;p.fill(Q(1));Four out;assert(!gamma_fused(a,b,prepare_beta(p,beta),out));assert(!gamma_original(a,b,p,beta,out));rejections++;}
 for(int len=0;len<404;len++)if(len!=403){Four out;std::array<Q,29>p{};assert(!gamma_fused(std::vector<uint8_t>(len),std::vector<uint8_t>(186),p,out));rejections++;}
 bool stale=false;std::array<Q,27>sent;for(auto&v:sent)v=random_q();Q x=random_q(),y=random_q();stale=semantic_cached(Q(3),sent,x,zero_boundary(y))!=semantic_reference(Q(3),sent,x);assert(stale);
 std::cout<<"{\"packed_lane_cases\":"<<packed_cases<<",\"schoolbook6_cases\":"<<product_cases<<",\"reduced_width_exhaustive_cases\":"<<reduced<<",\"whole_dot_cases\":"<<dot_cases<<",\"semantic_cache_rounds\":"<<semantic_cases<<",\"sparse_terminal_cases\":"<<sparse_cases<<",\"independent_full_chord_cases\":12,\"digest_factoring_cases\":"<<digest_cases<<",\"fused_gamma_cases\":"<<gamma_cases<<",\"malformed_rejections\":"<<rejections<<",\"stale_cache_negative\":true,\"all_passed\":true,\"aspis_rust_executed\":false,\"sbf_executed\":false}"<<std::endl;
}
