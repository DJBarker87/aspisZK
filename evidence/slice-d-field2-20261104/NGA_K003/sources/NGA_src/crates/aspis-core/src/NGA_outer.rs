use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(x:QM31)->bool{x.c0.a.0<P&&x.c0.b.0<P&&x.c1.a.0<P&&x.c1.b.0<P}
struct Log{before:[[u64;3];3],left:QM31,right:QM31,reply:[[u64;3];3],count:usize}
fn cut(log:&mut Log,sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3]{
 assert!(canonical(left)&&canonical(right));
 log.before=sums;log.left=left;log.right=right;log.count+=1;
 let reply:[[u64;3];3]=kani::any();log.reply=reply;reply
}
fn step<const N:usize>(mut sums:[[u64;3];3],left:[QM31;N],right:[QM31;N],mut index:usize,log:&mut Log)->([[u64;3];3],usize){
        sums = cut(log,sums, left[index], right[index]);
        index += 1;
(sums,index)
}
fn check<const N:usize>(left:[QM31;N],right:[QM31;N]){
 let sums:[[u64;3];3]=kani::any();let index:usize=kani::any();kani::assume(index<N);
 kani::assume(canonical(left[index])&&canonical(right[index]));
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);
 let old=sums[i][j];let expected_left=left[index];let expected_right=right[index];
 let mut log=Log{before:kani::any(),left:any_q(),right:any_q(),reply:kani::any(),count:0};
 let(out,next)=step(sums,left,right,index,&mut log);
 assert!(log.count==1&&next==index+1);
 assert!(log.before[i][j]==old&&log.left==expected_left&&log.right==expected_right);
 let want=log.reply[i][j];assert!(out[i][j]==if cfg!(NGA_invert){want^1}else{want});
}

#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn outer2(){check([any_q(),any_q()],[any_q(),any_q()]);}

#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn outer3(){check([any_q(),any_q(),any_q()],[any_q(),any_q(),any_q()]);}

#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn outer4(){check([any_q(),any_q(),any_q(),any_q()],[any_q(),any_q(),any_q(),any_q()]);}

#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let src:[[u64;3];3]=kani::any();let mut dst:[[u64;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]==dst[i][j]);}

#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src:[[u64;3];3]=kani::any();let mut dst:[[u64;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]!=dst[i][j]);}
