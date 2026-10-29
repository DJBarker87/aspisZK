fn main(){
 assert!(!cfg!(debug_assertions));
 let negative=std::env::args().any(|x|x=="--negative");
 for raw in 0..=u16::MAX as u32 {
  let mask=raw as u16;
  let mut expected_trailing=0u32;
  while expected_trailing<16 && (raw & (1<<expected_trailing))==0 {expected_trailing+=1;}
  let mut expected_population=0u32;
  for bit in 0..16 {if raw & (1<<bit)!=0 {expected_population+=1;}}
  if negative&&raw==3 {expected_trailing+=1;}
  assert_eq!(mask.trailing_zeros(),expected_trailing,"mask {mask}");
  assert_eq!(mask.count_ones(),expected_population,"mask {mask}");
  if mask!=0 {assert!(mask.trailing_zeros()<16);}
 }
 println!("exhaustive_u16_inputs=65536 trailing_and_population_comparisons=131072; deployed-configuration harness; V370 retained");
}
