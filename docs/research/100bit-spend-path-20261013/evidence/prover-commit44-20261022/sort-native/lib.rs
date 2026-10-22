// Exact native operations at sim.rs:477; no standard-library substitute.
fn native(mut indices:Vec<u32>)->Vec<u32> {indices.sort();indices.dedup();indices}
#[cfg(kani)] #[kani::proof] #[kani::unwind(40)]
fn sorted_distinct_membership() {
 let input:[u32;12]=kani::any();let len:usize=kani::any();kani::assume(len<=12);
 let indices=input[..len].to_vec();let out=native(indices);
 assert!(out.len()<=len);
 let i:usize=kani::any();
 if i<out.len().saturating_sub(1) {assert!(out[i]<out[i+1]);}
 let query:u32=kani::any();
 assert_eq!(input[..len].contains(&query),out.contains(&query));
}
