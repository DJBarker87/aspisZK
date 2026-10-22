
const ACTIVE_MASKS:[u16;64]=[
    6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
    2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214,
    1749,
];
fn native_s2_row(j:usize)->usize {
 const TAU:[usize;5]=[3,4,2,0,1];let mut out=0;
 for d in 0..5 {out|=((j>>(2*d))&3) << (2*TAU[d]);}out
}
fn native_s2_inactive(r:usize)->Result<bool,u8> {
 if r>=1024 {return Err(1);}
 Ok((ACTIVE_MASKS[r/16]>>(r%16))&1==0)
}
fn owner_s2_row(j:usize)->usize {(j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)}
fn owner_s2_inactive(j:usize)->bool {let r=owner_s2_row(j);(ACTIVE_MASKS[r/16]>>((r%16) as u32))&1==0}
#[cfg(kani)] mod inactive_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(66)] fn complete_s2_inactive() {
  let j:usize=kani::any();kani::assume(j<1024);
  assert_eq!(native_s2_row(j),owner_s2_row(j));
  assert_eq!(native_s2_inactive(native_s2_row(j)),Ok(owner_s2_inactive(j)));
 }
}
