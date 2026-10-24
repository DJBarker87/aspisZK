use crate::expand_values;

/// The reference loop is not re-executed in CBMC. Its full content law is a
/// separate Lean obligation; this gate checks the unchanged native function.
#[kani::proof]
#[kani::unwind(118)]
fn shipped_claims_all_bytes() {
    let input:[u8;1856]=kani::any();
    let mut output:[u8;3712]=kani::any();
    let watch:usize=kani::any();
    kani::assume(watch<3712);
    let result=expand_values(&input,&mut output);
    assert_eq!(result,Ok(()));
    assert_eq!(output.len(),3712);
    let byte=watch%32;
    if byte<16 {
        assert_eq!(output[watch],input[(watch/32)*16+byte]);
    } else {
        assert_eq!(output[watch],0);
    }
}
