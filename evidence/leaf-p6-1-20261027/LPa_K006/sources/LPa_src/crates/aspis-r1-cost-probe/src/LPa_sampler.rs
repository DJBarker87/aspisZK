//! Direct circle_sample on the reached rejected-parameter stage, no stubs.
use super::*;
#[kani::proof] #[kani::unwind(260)] fn LPa_circle_fallback(){
 let second:bool=kani::any();let row=if second{CircleRow::Second}else{CircleRow::First};
 assert_eq!(circle_sample(&[0u8;32],row),aspis_core::transcript::circle_fallback_point(usize::from(second)));
}
