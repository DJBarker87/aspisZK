use super::*;
#[test]
fn strict_scan_all_lengths_and_positions() {
 for len in 0..=480 {
  let mut bytes=vec![0;len];
  assert_eq!(check_values(&bytes),check_values_owned(&bytes));
  for at in 0..len {
   bytes[at]=255;
   assert_eq!(check_values(&bytes),check_values_owned(&bytes));
   bytes[at]=0;
  }
  for chunk in 0..len/16 { for limb in 0..4 {
   let at=chunk*16+limb*4;
   bytes[at..at+4].copy_from_slice(&0x7fffffffu32.to_le_bytes());
   assert_eq!(check_values(&bytes),Err(CodecError::NonCanonical));
   assert_eq!(check_values(&bytes),check_values_owned(&bytes));
   bytes[at..at+4].fill(0);
  }}
 }
}
#[test]
fn finish_every_prefix_and_extreme_residues() {
 for n in [0,1,4,64,256] {
  let raw:Vec<_>=(0..n).map(|i|[i as u64,u64::MAX,1<<63,0x7fffffff]).collect();
  for len in 0..=n {
   let mut weights=vec![K::ONE;len];
   let pending=BatchedWeights{raw:raw.clone(),terms:3};pending.finish(&mut weights);
   assert_eq!(weights,finish_owned(raw.clone(),vec![K::ONE;len]));
  }
 }
}
#[test]
fn residue_every_phase_and_extreme() {
 for phase in 0..4 { for limb in [0,1,0x7ffffffe] { for basis in [0,1,0x7ffffffe] {
  let power=K{c0:CM31{a:M31(limb),b:M31(limb)},c1:CM31{a:M31(limb),b:M31(limb)}};
  let raw=[(1u64<<34)-1+phase*0x7ffffffeu64*0x7ffffffeu64;4];
  let mut expected=raw;update_residue_row(&mut expected,power,M31(basis),phase==3);
  assert_eq!(expected,residue_owned(raw,power,M31(basis),phase==3));
 }}}
}
