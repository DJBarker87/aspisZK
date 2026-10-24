use crate::{expand_values,y1_owned_reference,CodecError};

// Native source/reference equivalence on every byte of the complete Y1
// buffers. Both sides receive the same arbitrary input and initial output.
#[kani::proof]
#[kani::unwind(34)]
fn shipped_y1_owned_equivalent() {
    let input:[u8;464]=kani::any();
    let initial:[u8;928]=kani::any();
    let mut shipped=initial;
    let watch:usize=kani::any();
    kani::assume(watch<928);
    let shipped_status=expand_values(&input,&mut shipped);
    let (owned_status,owned)=y1_owned_reference(input,initial);
    assert_eq!(shipped_status,owned_status);
    assert_eq!(shipped[watch],owned[watch]);
}

// Split out the actual Y1 input shape. This avoids the previous OR of two
// symbolic lengths. Output lengths >928 are covered up to this explicit cap;
// no universal unbounded-metadata or whole-caller claim is made.
#[kani::proof]
#[kani::unwind(34)]
fn shipped_y1_output_length_error_frame() {
    let input:[u8;464]=kani::any();
    let mut output:[u8;1856]=kani::any();
    let output_len:usize=kani::any();
    let watch:usize=kani::any();
    kani::assume(output_len<=1856);
    kani::assume(output_len!=928);
    kani::assume(watch<1856);
    let before=output[watch];
    let result=expand_values(&input,&mut output[..output_len]);
    assert_eq!(result,Err(CodecError::Length));
    assert_eq!(output[watch],before);
}
