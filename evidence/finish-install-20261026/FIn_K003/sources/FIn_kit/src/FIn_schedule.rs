// P6 iterator/control certificate. Arithmetic is checked separately by the
// extracted actual primitive theorems; this tests the standard iterator used
// by the exact shipped polynomial body, including empty fold state.
#[kani::proof]
#[kani::unwind(9)]
fn FIn_polynomial_schedule() {
    let (trace,count)=(0usize..7).rev().fold(([99usize;7],0usize),|(mut trace,count),i| {
        trace[count]=i; (trace,count+1)
    });
    assert_eq!(count,7);
    assert!(trace[0]==6 && trace[1]==5 && trace[2]==4 && trace[3]==3 && trace[4]==2 && trace[5]==1 && trace[6]==0);
}
