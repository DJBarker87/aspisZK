use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
struct Log{a:[u64;4],b:[u64;4],reply:[u64;4],count:usize}
fn product(log:&mut Log,a:u64,b:u64)->u64{assert!(a<P as u64&&b<P as u64&&log.count<4);let r:u64=kani::any();kani::assume(r<1u64<<62);log.a[log.count]=a;log.b[log.count]=b;log.reply[log.count]=r;log.count+=1;r}
fn term_cut(mut raw:[u64;4],weight:QM31,value:u64,log:&mut Log)->[u64;4]{
 raw[0]+=product(log,u64::from(weight.c0.a.0),value);
 raw[1]+=product(log,u64::from(weight.c0.b.0),value);
 raw[2]+=product(log,u64::from(weight.c1.a.0),value);
 raw[3]+=product(log,u64::from(weight.c1.b.0),value);raw
}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn term_step(){let raw:[u64;4]=kani::any();for i in 0..4{kani::assume(raw[i]<3u64*(1u64<<62));}let weight=any_q();let value:u32=kani::any();kani::assume(canonical(weight)&&value<P);let mut log=Log{a:[0;4],b:[0;4],reply:[0;4],count:0};let got=term_cut(raw,weight,value as u64,&mut log);let i:usize=kani::any();kani::assume(i<4);let a=match i{0=>weight.c0.a.0,1=>weight.c0.b.0,2=>weight.c1.a.0,_=>weight.c1.b.0};assert!(log.count==4&&log.a[i]==a as u64&&log.b[i]==value as u64);let want=raw[i]+log.reply[i];assert!(got[i]==if cfg!(NFT_invert){want^1}else{want});}
fn fold_cut(mut sums:[u64;4],raw:[u64;4])->[u64;4]{for index in 0..4{sums[index]+=M31::reduce_u64(raw[index]).0 as u64;}sums}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn fold_step(){let sums:[u64;4]=kani::any();let raw:[u64;4]=kani::any();for i in 0..4{kani::assume(sums[i]<=20u64*(P as u64));}let got=fold_cut(sums,raw);let i:usize=kani::any();kani::assume(i<4);let want=sums[i]+M31::reduce_u64(raw[i]).0 as u64;assert!(got[i]==if cfg!(NFT_invert){want^1}else{want});}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn short_control(){let n:usize=kani::any();kani::assume(n<=4);let mut indices=[99usize;4];let mut index=0usize;while index<n{indices[index]=index;index+=1;}assert!(index==n);if n>0{let at:usize=kani::any();kani::assume(at<n);assert!(indices[at]==if cfg!(NFT_invert){at+1}else{at});}else{assert!(!cfg!(NFT_invert));}}
struct Control{pairs:[(usize,usize);80],starts:[usize;20],terms:usize,cuts:usize,folds:usize}
fn control(n:usize,log:&mut Control){for start in (0..n).step_by(4){log.starts[log.cuts]=start;log.cuts+=1;let end=core::cmp::min(start+4,n);for index in start..end{log.pairs[log.terms]=(start,index);log.terms+=1;}for _index in 0..4{log.folds+=1;}}}
#[kani::proof] #[kani::unwind(110)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn long_control(){let n:usize=kani::any();kani::assume(n>4&&n<=80);let mut log=Control{pairs:[(99,99);80],starts:[99;20],terms:0,cuts:0,folds:0};control(n,&mut log);let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<n&&j<(n+3)/4);assert!(log.terms==n&&log.cuts==(n+3)/4&&log.folds==4*log.cuts);assert!(log.starts[j]==j*4);assert!(log.pairs[i]==if cfg!(NFT_invert){((i/4)*4,i+1)}else{((i/4)*4,i)});}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_copy_positive(){let src:[u64;4]=kani::any();let mut dst:[u64;4]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();kani::assume(i<4);assert!(src[i]==dst[i]);}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_copy_negative(){let src:[u64;4]=kani::any();let mut dst:[u64;4]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();kani::assume(i<4);assert!(src[i]!=dst[i]);}
