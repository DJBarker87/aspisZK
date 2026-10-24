use crate::{expand_values,values_owned_reference};
use alloc::vec::Vec;

fn compare<const I:usize,const O:usize>() {
    let input:[u8;I]=kani::any();
    let initial:[u8;O]=kani::any();
    let mut shipped=initial;
    let watch:usize=kani::any();
    let input_watch:usize=kani::any();
    kani::assume(watch<O);
    kani::assume(input_watch<I);
    let status=expand_values(&input,&mut shipped);
    let (owned_status,owned_input,owned_output)=
        values_owned_reference(Vec::from(&input[..]),Vec::from(&initial[..]));
    assert_eq!(status,owned_status);
    assert_eq!(owned_input.len(),I);
    assert_eq!(owned_output.len(),O);
    assert_eq!(input[input_watch],owned_input[input_watch]);
    assert_eq!(shipped[watch],owned_output[watch]);
}
#[kani::proof] #[kani::unwind(34)]
fn shipped_y1_vec_owned_equivalent(){compare::<464,928>();}
#[kani::proof] #[kani::unwind(34)]
fn shipped_row14_vec_owned_equivalent(){compare::<16,32>();}
#[kani::proof] #[kani::unwind(34)]
fn shipped_polynomial_vec_owned_equivalent(){compare::<448,896>();}
#[kani::proof] #[kani::unwind(130)]
fn shipped_claims_vec_owned_equivalent(){compare::<1856,3712>();}
