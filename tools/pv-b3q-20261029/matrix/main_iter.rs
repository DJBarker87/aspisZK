mod field;
use field::{M31,CM31,QM31};
fn q(n:u32)->QM31 {QM31{c0:CM31{a:M31(n),b:M31(n*17)},c1:CM31{a:M31(n*31),b:M31(n*47)}}}
fn main(){
 assert!(!cfg!(debug_assertions));assert_eq!(core::mem::size_of::<QM31>(),16);
 let negative=std::env::args().any(|s|s=="--negative");let mut comparisons=0;
 for seed in [0u32,1,7,19] {
  let mut cells:[QM31;4]=core::array::from_fn(|i|q((seed+1)*31+i as u32));
  let before=cells;let mut expected=before;
  for i in 0..4 {expected[i]=q((seed+1)*73+i as u32);}
  { let mut it=cells.iter_mut().enumerate();
    for i in 0..4 {let (group,slot)=it.next().unwrap();assert_eq!(group,i);assert_eq!(*slot,before[i]);
      if !(negative&&seed==0&&i==2){*slot=q((seed+1)*73+i as u32);}comparisons+=2;
    }
    assert!(it.next().is_none());assert!(it.next().is_none());comparisons+=2;
  }
  assert_eq!(cells,expected,"all four restored mutable slots, seed {seed}");assert_ne!(cells,before);comparisons+=2;
 }
 println!("iterator_comparisons={comparisons}; exact QM31 non-ZST specialization, four mutable stores and both terminal None checks");
}
