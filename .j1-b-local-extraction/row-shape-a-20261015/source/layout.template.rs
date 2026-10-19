#![no_std]
#![allow(dead_code)]
pub mod r1_wire {
    include!("fragments/lanes.rs");
    include!("fragments/points.rs");
    include!("fragments/claims.rs");
    include!("fragments/row_shape.rs");
}
