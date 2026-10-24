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

