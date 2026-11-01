use aspis_core::field::{M31,CM31,QM31};
use super::clear_source;
#[kani::proof]
#[kani::unwind(36)]
fn salt_cell_frame() {
    let mut cells:[[u8;32];3]=kani::any();let old=cells;
    let at:usize=kani::any();kani::assume(at<3);
    clear_source::clear_private_salt(&mut cells[at]);
    for i in 0..3 {assert_eq!(cells[i],if i==at {[0;32]} else {old[i]});}
}
#[kani::proof]
#[kani::unwind(8)]
fn m31_cell_frame() {
    let raw:[u32;3]=kani::any();let mut cells=[M31(raw[0]),M31(raw[1]),M31(raw[2])];let old=cells;
    let at:usize=kani::any();kani::assume(at<3);
    clear_source::volatile_clear_cell(&mut cells[at],M31::ZERO);
    for i in 0..3 {assert_eq!(cells[i],if i==at {M31::ZERO} else {old[i]});}
}
fn q(a:[u32;4])->QM31 {QM31{c0:CM31::new(M31(a[0]),M31(a[1])),c1:CM31::new(M31(a[2]),M31(a[3]))}}
#[kani::proof]
#[kani::unwind(8)]
fn qm31_cell_frame() {
    let raw:[[u32;4];3]=kani::any();let mut cells=[q(raw[0]),q(raw[1]),q(raw[2])];let old=cells;
    let at:usize=kani::any();kani::assume(at<3);
    clear_source::volatile_clear_cell(&mut cells[at],QM31::ZERO);
    for i in 0..3 {assert_eq!(cells[i],if i==at {QM31::ZERO} else {old[i]});}
}
