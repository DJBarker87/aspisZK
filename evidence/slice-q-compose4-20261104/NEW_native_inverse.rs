use aspis_core::field::M31;
fn main(){
 let bad=std::env::args().any(|x|x=="--bad");
 assert!(std::panic::catch_unwind(||M31(0).inv()).is_err());
 println!("zero:assertionFailure");
 let cases:[(u32,u32);10]=[(1,1),(2,1073741824),(3,1431655765),(2147483646,2147483646),(2147483647,0),(2147483648,1),(4294967295,1),(17,252645135),(123456789,391219981),(3735928559,903932218)];
 for (i,(x,expected)) in cases.into_iter().enumerate(){
  let actual=M31(x).inv().0;
  println!("{x}:{actual}");
  let expected=if bad&&i==0 {expected^1} else {expected};
  assert_eq!(actual,expected);
 }
}
