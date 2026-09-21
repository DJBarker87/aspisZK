#include "model.hpp"
uint64_t seed_=0x1f978cbadb42e279ULL;
U rnd(){seed_^=seed_<<13;seed_^=seed_>>7;seed_^=seed_<<17;return U(seed_%P);}
F randf(){return Q(C(B(rnd()),B(rnd())),C(B(rnd()),B(rnd())));}
V xt_read(const V&v,int n){V o(n);for(int j=0;j<n;j++)for(auto rs:edges(j)){assert(rs.first<int(v.size()));o[j]=o[j]+v[rs.first]*rs.second;}return o;}
V transpose(const V&w,std::array<F,3>abc){V e(514),o(514);for(int j=0;j<512;j++){e[j]=w[2*j];o[j]=w[2*j+1];}auto xe=xt_read(e,513),xxe=xt_read(xe,512),xo=xt_read(o,512);V out(1024);for(int j=0;j<512;j++){out[2*j]=abc[0]*e[j]+abc[1]*xe[j]+abc[2]*o[j];out[2*j+1]=abc[2]*(e[j]-xxe[j])+abc[0]*o[j]+abc[1]*xo[j];}return out;}
V dfold(const V&v,F a){V r(v.size()/4);for(size_t j=0;j<r.size();j++)r[j]=(v[4*j]+a*(v[4*j+3]+a*(v[4*j+2]+a*v[4*j+1]))).half().half();return r;}
int main(){Transport t(2);int cases=0,folds=0;bool naive=false;auto ss=slots("stride3");
 for(int c=0;c<48;c++){
  std::array<F,10>z;for(auto&v:z)v=randf();auto pts=statement(z);std::array<F,3>abc;for(auto&v:abc)v=randf();F k=randf(),tau=randf(),beta=c==0?F():c==1?F(1):c==2?-F(1):randf(),om=F(1)-beta;
  auto e0=t.dual(mle(pts[0])),e1=t.dual(mle(pts[1])),e2=t.dual(mle(pts[2])),cw=coinweights(z);V h(1024),a(1024),b(1024),merged(1024);for(int i=0;i<271;i++)h[ss[i]]=cw[i];F k2=k*k,k3=k2*k;
  for(int j=0;j<1024;j++){a[j]=k*e0[j]+k2*e1[j]+k3*e2[j]+F(j==1023);b[j]=k2*e1[j]+k3*e2[j]+k*h[j]+F(j==1023);merged[j]=om*k*e0[j]+k2*e1[j]+k3*e2[j]+beta*k*h[j]+F(j==1023);}
  auto wr=transpose(a,abc),wg=transpose(b,abc),wb=transpose(merged,abc);F t2=tau*tau,t3=t2*tau,t4=t2*t2;
  wr[1023]=wr[1023]+tau;wr[1022]=wr[1022]+t2*abc[1];wr[1021]=wr[1021]-t2*abc[2];wg[1023]=wg[1023]+t3;wg[1022]=wg[1022]+t4*abc[1];wg[1021]=wg[1021]-t4*abc[2];F i0=om*tau+beta*t3,i1=om*t2+beta*t4;wb[1023]=wb[1023]+i0;wb[1022]=wb[1022]+i1*abc[1];wb[1021]=wb[1021]-i1*abc[2];
  V qr(1024),qg(1024),qb(1024),dq(1024),dw(1024);for(int j=0;j<1024;j++){qr[j]=randf();qg[j]=randf();qb[j]=om*qr[j]+beta*qg[j];dq[j]=qg[j]-qr[j];dw[j]=wg[j]-wr[j];assert(wb[j]==om*wr[j]+beta*wg[j]);}
  // Arbitrary high/image residual coordinates: no honest-generation premise.
  F p0=dot(qr,wr),p2=dot(dq,dw),claim=dot(qr,wr)+dot(qg,wg),p1=claim-F(2)*p0-p2;assert(p0+beta*(p1+beta*p2)==dot(qb,wb));if(dot(qb,wb)!=claim)naive=true;
  for(int r=0;r<4;r++){F alpha=randf();wr=dfold(wr,alpha);wg=dfold(wg,alpha);wb=dfold(wb,alpha);for(size_t j=0;j<wb.size();j++)assert(wb[j]==om*wr[j]+beta*wg[j]);folds++;}cases++;
 }assert(naive);
 int polynomials=0,maxroots=0,roots_total=0;for(int a=0;a<31;a++)for(int b=0;b<31;b++)for(int c=0;c<31;c++){if((2*a+b+c)%31==0)continue;int roots=0;for(int x=0;x<31;x++)if((a+b*x+c*x*x)%31==0)roots++;assert(roots<=2);maxroots=std::max(maxroots,roots);roots_total+=roots;polynomials++;}assert(maxroots==2);
 std::cout<<"{\"source_shaped_weight_cases\":"<<cases<<",\"arbitrary_image_residuals\":true,\"fold_stages\":"<<folds<<",\"false_boundary_polynomials_F31\":"<<polynomials<<",\"roots_total\":"<<roots_total<<",\"max_roots\":"<<maxroots<<",\"old_field_allocation\":953,\"candidate_field_allocation\":699,\"all_passed\":true,\"sbf_executed\":false,\"full_soundness_proved\":false,\"full_privacy_proved\":false}\n";
}
