use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct NoHash<'a>(&'a Cell<usize>);
impl Digest32 for NoHash<'_>{fn digest(&self,_:&[&[u8]])->[u8;32]{self.0.set(self.0.get()+1);panic!("unreached digest")}}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_invalid_n_frame(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();kani::assume(n==0||n>16);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);assert!(!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_invalid_n_frame_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();kani::assume(n==0||n>16);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);assert!(!(!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_first_pair_rejection_frame(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();kani::assume(n>=2&&n<=16&&idx[0]>=idx[1]);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);assert!(!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_first_pair_rejection_frame_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();kani::assume(n>=2&&n<=16&&idx[0]>=idx[1]);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);assert!(!(!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_return_frame(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();let at:usize=kani::any();let len:usize=kani::any();let leaf_ok=n==1&&index_at(&idx,0)==0&&root_matches(&val,&root)&&at==len;let result:Result<(),u8>=if !leaf_ok{Err(1)}else{Ok(())};assert!(result.is_ok()==(n==1&&idx[0]==0&&val[0]==root&&at==len)&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_return_frame_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let n:usize=kani::any();let at:usize=kani::any();let len:usize=kani::any();let leaf_ok=n==1&&index_at(&idx,0)==0&&root_matches(&val,&root)&&at==len;let result:Result<(),u8>=if !leaf_ok{Err(1)}else{Ok(())};assert!(!(result.is_ok()==(n==1&&idx[0]==0&&val[0]==root&&at==len)&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_level_carrier_transition(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let depth:u32=kani::any();let w:usize=kani::any();let mut n:usize=kani::any();let at:usize=kani::any();kani::assume(depth<18&&n>0&&n<=16&&w>0&&w<=n&&at<=5504);n=w;let mut levels=depth+1..Arity::Two.levels();let next=levels.next();let i=0usize;let next_w=0usize;assert!(n==w&&n<=16&&i<=n&&next_w<=i&&at<=5504&&next==if depth<17{Some(depth+1)}else{None}&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_verify_level_carrier_transition_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let depth:u32=kani::any();let w:usize=kani::any();let mut n:usize=kani::any();let at:usize=kani::any();kani::assume(depth<18&&n>0&&n<=16&&w>0&&w<=n&&at<=5504);n=w;let mut levels=depth+1..Arity::Two.levels();let next=levels.next();let i=0usize;let next_w=0usize;assert!(!(n==w&&n<=16&&i<=n&&next_w<=i&&at<=5504&&next==if depth<17{Some(depth+1)}else{None}&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior));}
