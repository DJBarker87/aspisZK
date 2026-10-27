// K004 split: all64 shipped updates execute, one16-cell output block checked.
#[kani::proof] #[kani::unwind(65)]
fn FJd_tensor64_block0() {
 let mut w=empty();for d in 2..5 {for s in 0..4 {w.factors[0][d][s]=any_k();}}
 let mut out=[K::ZERO;64];w.tensor(0,2,&mut out);
 let expected=tensor_reference(&w.factors[0]);
 for j in 0..16 {assert_eq!(out[j],expected[j]);}
 kani::cover!(true,"canonical factors, first16 outputs of full64 tensor");
}
