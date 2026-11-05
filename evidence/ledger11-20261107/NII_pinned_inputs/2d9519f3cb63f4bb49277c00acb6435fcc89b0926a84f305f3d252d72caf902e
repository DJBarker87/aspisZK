use super::*;
use aspis_core::field::CM31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_q()->K{K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_e()->E{let x:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(x[i]<2147483647);i+=1;}E::from_limbs(x).unwrap()}
struct T{state:[u8;32],hash:u64}
struct Log{row:u8,len:usize,position:usize,byte:u8,nonzero:bool,before:[u8;32],after:[u8;32],value:E,q:K,calls:usize}
impl T{
 fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool,log:&mut Log)->E{
  log.row=row;log.len=payload.len();log.byte=if log.position<payload.len(){payload[log.position]}else{0};log.nonzero=nonzero;log.before=self.state;log.calls+=1;self.state=log.after;log.value
 }
 fn scalar_k(&mut self,row:u8,payload:&[u8],log:&mut Log)->K{
  log.row=row;log.len=payload.len();log.byte=if log.position<payload.len(){payload[log.position]}else{0};log.before=self.state;log.calls+=1;self.state=log.after;log.q
 }
}
fn log()->Log{Log{row:kani::any(),len:kani::any(),position:kani::any(),byte:kani::any(),nonzero:kani::any(),before:kani::any(),after:kani::any(),value:any_e(),q:any_q(),calls:0}}
fn scalar_stage(which:u8){
 let mut t=T{state:kani::any(),hash:kani::any()};let before=t.state;let hash=t.hash;
 let mut l=log();let next=l.after;let value=l.value;let q=l.q;
 // Complete arbitrary live scalar locals; stage must retain both untouched.
 let live_gamma=any_e();let live_kappa=any_e();let saved_gamma=live_gamma;let saved_kappa=live_kappa;
 let inactive=any_e();let y1:[u8;928]=kani::any();let round0:[u8;224]=kani::any();
 let pos=l.position;let row:u8=kani::any();kani::assume(row==30||row==31);
 let r=match which{
  0=>t.scalar(27,&y1,true,&mut l),
  1=>t.scalar(28,&inactive.to_le_bytes(),false,&mut l),
  2=>t.scalar(29,&round0,false,&mut l),
  _=>{let rho=t.scalar_k(row+1,&[],&mut l);assert_eq!(rho,q);value}
 };
 let expected=match which{0=>if pos<928{y1[pos]}else{0},1=>if pos<32{inactive.to_le_bytes()[pos]}else{0},2=>if pos<224{round0[pos]}else{0},_=>0};
 let good=r==value&&l.calls==1&&l.row==match which{0=>27,1=>28,2=>29,_=>row+1}&&l.len==match which{0=>928,1=>32,2=>224,_=>0}&&l.byte==expected&&(which==3||l.nonzero==(which==0))&&l.before==before&&t.state==next&&t.hash==hash&&live_gamma==saved_gamma&&live_kappa==saved_kappa;
 assert!(good!=cfg!(NGN_invert));
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn gamma_stage(){scalar_stage(0)}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn kappa_stage(){scalar_stage(1)}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn alpha0_stage(){scalar_stage(2)}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn rho_stage(){scalar_stage(3)}

fn es()->[E;29]{let mut xs=[E::ZERO;29];let mut i=0;while i<29{xs[i]=any_e();i+=1;}xs}
fn power(gamma:E,log:&mut E,reply:[E;29])->[E;29]{*log=gamma;reply}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn powers_assignment(){let gamma=any_e();let kappa=any_e();let saved_kappa=kappa;let state:[u8;32]=kani::any();let saved_state=state;let reply=es();let mut g=es();let mut log=any_e();let i:usize=kani::any();kani::assume(i<29);
 *&mut g=power(gamma,&mut log,reply);
 assert!((g[i]==reply[i]&&log==gamma&&kappa==saved_kappa&&state==saved_state)!=cfg!(NGN_invert));
}
