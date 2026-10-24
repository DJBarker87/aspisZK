#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#[cfg(kani)]
fn early(stop:usize)->Result<usize,()> {
 let mut count=0usize;
 #[kani::loop_invariant(count==kani::index)]
 for i in 0usize..6usize {if i==stop{return Err(());} count+=1;}
 Ok(count)
}
#[cfg(kani)]
#[kani::proof]
fn range_loop_contract() {
 let stop:usize=kani::any();
 assert_eq!(early(stop),if stop<6{Err(())}else{Ok(6)});
}
