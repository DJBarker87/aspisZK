use crate::{expand_values,CodecError};

// An asserted-unreachable cut, not a behavioral assumption. If execution
// reaches the loop constructor under the rejection precondition, verification
// fails on this panic. Positive body proofs use NO stubs.
fn forbidden_chunks<T>(_:&[T],_:usize)->core::slice::ChunksExact<'_,T> {
    panic!("native positive-body constructor reached on length rejection");
}

#[kani::proof]
#[kani::stub(<[u8]>::chunks_exact,forbidden_chunks)]
#[kani::unwind(2)]
fn shipped_y1_reject_before_body() {
    let input:[u8;464]=kani::any();
    let mut output:[u8;1856]=kani::any();
    let output_len:usize=kani::any();
    let watch:usize=kani::any();
    kani::assume(output_len<=1856);
    kani::assume(output_len!=928);
    kani::assume(watch<1856);
    kani::cover!(output_len==0,"empty output is represented");
    kani::cover!(output_len==1856,"oversized output is represented");
    let before=output[watch];
    let result=expand_values(&input,&mut output[..output_len]);
    assert_eq!(result,Err(CodecError::Length));
    assert_eq!(output[watch],before);
}
