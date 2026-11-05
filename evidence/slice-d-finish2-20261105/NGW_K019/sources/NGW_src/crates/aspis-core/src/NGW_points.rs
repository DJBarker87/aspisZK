use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn q(w:[u32;4])->QM31{QM31{c0:crate::field::CM31{a:crate::field::M31(w[0]),b:crate::field::M31(w[1])},c1:crate::field::CM31{a:crate::field::M31(w[2]),b:crate::field::M31(w[3])}}}
fn anyq()->QM31{let w:[u32;4]=kani::any();for a in w{kani::assume(a<2147483647);}q(w)}
fn add(x:u32,y:u32)->u32{let s=x+y;if s>=2147483647{s-2147483647}else{s}}
fn sub(x:u32,y:u32)->u32{if x>=y{x-y}else{x+2147483647-y}}
struct Log{reply:QM31,left:[u32;4],right:[u32;4],calls:usize}
fn product(bit:QM31,carry:QM31,log:&mut Log)->QM31{log.left=words(bit);log.right=words(carry);log.calls+=1;log.reply}
fn step(z:&[QM31;10],successor:&mut[QM31;10],carry:&mut QM31,coordinate:usize,log:&mut Log){
 let bit = z[coordinate];
 let bit_and_carry = product(bit,*carry,log);
 successor[coordinate] = bit.add(*carry).sub(bit_and_carry.add(bit_and_carry));
 *carry = bit_and_carry;
}
fn exercise(g:u8){let z=core::array::from_fn(|_|anyq());let mut s=core::array::from_fn(|_|anyq());let before=s;let mut carry=anyq();let old=carry;let p=anyq();let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<10);let mut log=Log{reply:p,left:[0;4],right:[0;4],calls:0};
 step(&z,&mut s,&mut carry,i,&mut log);
 let expected=sub(add(words(z[i])[j],words(old)[j]),add(words(p)[j],words(p)[j]));
 if cfg!(NGW_invert){match g{0=>{let mut w=words(s[i]);w[j]^=1;s[i]=q(w)},1=>log.left[j]^=1,2=>{let mut w=words(carry);w[j]^=1;carry=q(w)},3=>{let mut w=words(s[k]);w[j]^=1;s[k]=q(w)},_=>log.calls+=1}}
 assert!(match g{0=>words(s[i])[j]==expected,1=>log.left==words(z[i])&&log.right==words(old),2=>words(carry)==words(p),3=>words(s[k])[j]==if k==i{expected}else{words(before[k])[j]},_=>log.calls==1});
}
fn absorb(g:u8){let mut a=core::array::from_fn::<_,10,_>(|_|anyq());let old=a;let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<10);
 a[7]=QM31::ONE.sub(a[7]);a[6]=QM31::ONE.sub(a[6]);
 if cfg!(NGW_invert){let mut w=words(a[k]);w[j]^=1;a[k]=q(w);}
 let one=if j==0{1}else{0};let expected=if k==7||k==6{sub(one,words(old[k])[j])}else{words(old[k])[j]};assert!(words(a[k])[j]==expected);let _=g;
}
fn control(){let z=[QM31::ZERO;10];let mut n=0;let mut trace=[0usize;10];for coordinate in (0..z.len()).rev(){trace[n]=coordinate;n+=1;}let j:usize=kani::any();kani::assume(j<10);if cfg!(NGW_invert){trace[j]^=1;}assert!(n==10&&trace[j]==9-j);}
fn copy_control(){let a:[u8;160]=kani::any();let mut b:[u8;160]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<160);if cfg!(NGW_invert){b[i]^=1;}assert!(a[i]==b[i]);}
macro_rules! gate{($n:ident,$f:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(161)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $n(){$f($g)}};}
gate!(step_g0,exercise,0);
gate!(step_g1,exercise,1);
gate!(step_g2,exercise,2);
gate!(step_g3,exercise,3);
gate!(step_g4,exercise,4);
gate!(absorption,absorb,0);
#[kani::proof]#[kani::unwind(161)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn control_gate(){control()}
#[kani::proof]#[kani::unwind(161)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn copy_control_gate(){copy_control()}

struct WrapperLog{reply:[[QM31;10];3],args:[QM31;10],ptr:*const QM31,calls:usize}
fn point_reply(alpha:&[QM31;10],log:&mut WrapperLog)->[[QM31;10];3]{log.args=*alpha;log.ptr=alpha.as_ptr();log.calls+=1;log.reply}
fn source_wrapper(alpha:&[QM31;10],log:&mut WrapperLog)->[[QM31;10];3]{point_reply(alpha,log)}
fn wrapper_exercise(g:u8){let alpha=core::array::from_fn(|_|anyq());let before=alpha;let reply=core::array::from_fn(|_|core::array::from_fn(|_|q(kani::any())));let mut log=WrapperLog{reply,args:[QM31::ZERO;10],ptr:core::ptr::null(),calls:0};let out=source_wrapper(&alpha,&mut log);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);
 if cfg!(NGW_invert){match g{0=>{let mut w=words(log.reply[p][i]);w[j]^=1;log.reply[p][i]=q(w)},1=>{let mut w=words(log.args[i]);w[j]^=1;log.args[i]=q(w)},2=>log.ptr=log.ptr.wrapping_add(1),3=>log.calls+=1,_=>{}}}
 assert!(match g{0=>words(out[p][i])[j]==words(log.reply[p][i])[j],1=>words(log.args[i])[j]==words(alpha[i])[j],2=>log.ptr==alpha.as_ptr(),3=>log.calls==1,_=>words(alpha[i])[j]==words(before[i])[j]});}
fn return_points(z:&[QM31;10],successor:[QM31;10],absorption:[QM31;10])->[[QM31;10];3]{[*z,successor,absorption]}
fn return_exercise(g:u8){let z=core::array::from_fn(|_|q(kani::any()));let successor=core::array::from_fn(|_|q(kani::any()));let absorption=core::array::from_fn(|_|q(kani::any()));let out=return_points(&z,successor,absorption);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let mut expected=words(match p{0=>z[i],1=>successor[i],_=>absorption[i]})[j];if cfg!(NGW_invert){expected^=1;}assert!(words(out[p][i])[j]==expected);let _=g;}
fn init_exercise(g:u8){let z=core::array::from_fn::<_,10,_>(|_|q(kani::any()));let successor=z;let carry=QM31::ONE;let absorption=z;let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let mut expected=words(z[i])[j];if cfg!(NGW_invert){expected^=1;}assert!(if g==0{words(successor[i])[j]==expected}else{words(absorption[i])[j]==expected});assert!(words(carry)==[1,0,0,0]);}
gate!(wrapper_g0,wrapper_exercise,0);
gate!(wrapper_g1,wrapper_exercise,1);
gate!(wrapper_g2,wrapper_exercise,2);
gate!(wrapper_g3,wrapper_exercise,3);
gate!(return_frame,return_exercise,0);
gate!(init_successor,init_exercise,0);
gate!(init_absorption,init_exercise,1);
