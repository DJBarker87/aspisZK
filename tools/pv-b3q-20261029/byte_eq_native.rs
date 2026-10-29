fn main(){
 assert!(!cfg!(debug_assertions));
 let negative=std::env::args().any(|s|s=="--negative");
 let mut comparisons=0usize;
 let empty:[u8;0]=[];assert!(empty==empty);comparisons+=1;
 for base in 0..=255u8 {
  let left=[base;32];assert!(left==left);comparisons+=1;
  for position in 0..32 {
   let mut right=left;right[position]^=1;
   let expected=negative&&base==0&&position==0;
   assert_eq!(left==right,expected,"base {base}, changed byte {position}");
   assert_eq!(left!=right,!expected);comparisons+=2;
  }
 }
 println!("byte_array_comparisons={comparisons}; every byte position changes the observed equality; finite validation only");
}
