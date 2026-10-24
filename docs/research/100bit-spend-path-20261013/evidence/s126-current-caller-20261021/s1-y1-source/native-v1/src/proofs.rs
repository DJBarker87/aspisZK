use crate::{expand_values,CodecError};

// Whole unchanged shipped helper, all 29 chunks. The symbolic watch index
// quantifies every output byte; input and initial output are arbitrary.
#[kani::proof]
#[kani::unwind(34)]
fn shipped_y1_all_bytes() {
    let input:[u8;464]=kani::any();
    let mut output:[u8;928]=kani::any();
    let watch:usize=kani::any();
    kani::assume(watch<928);
    let before_len=output.len();
    let result=expand_values(&input,&mut output);
    assert_eq!(result,Ok(()));
    assert_eq!(output.len(),before_len);
    let chunk=watch/32;
    let within=watch%32;
    let expected=if within<16 {input[chunk*16+within]} else {0};
    assert_eq!(output[watch],expected);
}

// Guard rejection is checked with every bounded input/output length and byte.
// This does not assert whole-function totality on unbounded slice metadata.
#[kani::proof]
#[kani::unwind(34)]
fn shipped_y1_length_error_frame() {
    let input:[u8;464]=kani::any();
    let mut output:[u8;928]=kani::any();
    let input_len:usize=kani::any();
    let output_len:usize=kani::any();
    let watch:usize=kani::any();
    kani::assume(input_len<=464);
    kani::assume(output_len<=928);
    kani::assume(watch<928);
    kani::assume(input_len%16!=0 || output_len!=2*input_len);
    let before=output[watch];
    let result=expand_values(&input[..input_len],&mut output[..output_len]);
    assert_eq!(result,Err(CodecError::Length));
    assert_eq!(output[watch],before);
}
