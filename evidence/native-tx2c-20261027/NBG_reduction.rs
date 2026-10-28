#[kani::proof]
fn NBG_reduce_all_u64(){
 let x:u64=kani::any();let p=super::P as u64;
 let first=((x as u128)&(p as u128))+((x as u128)>>31);
 let second=(first&(p as u128))+(first>>31);
 assert!(first<=u64::MAX as u128 && second<=p as u128+3);
 let expected=if second>=p as u128{second-p as u128}else{second};
 assert!(super::reduce_u64(x)as u128==expected);
 assert!(super::M31::reduce_u64(x).0 as u128==expected);
 assert!(expected<p as u128);
 kani::cover!(x==u64::MAX);
}
