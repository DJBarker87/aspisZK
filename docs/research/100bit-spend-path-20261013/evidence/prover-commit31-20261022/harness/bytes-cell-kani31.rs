#[cfg(kani)]
mod bytes_cell_kani31 {
    use super::*;
    #[kani::proof] #[kani::unwind(12)]
    fn wide_byte() {
        let limbs:[u32;8]=kani::any();
        for limb in limbs {kani::assume(limb<aspis_core::field::P);}
        let value=E::from_limbs(limbs).unwrap();
        let at:usize=kani::any();kani::assume(at<32);
        assert_eq!(owned31::wide_bytes(value)[at],value.to_le_bytes()[at]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn cell_transition() {
        let values:[[u32;29];4]=kani::any();let value:u32=kani::any();
        let row:usize=kani::any();let lane:usize=kani::any();
        kani::assume(row<4 && lane<29);
        let mut native=values;native[row][lane]=value;
        let actual=owned31::put_cell(values,row,lane,value);
        let r:usize=kani::any();let l:usize=kani::any();kani::assume(r<4 && l<29);
        assert_eq!(actual[r][l],native[r][l]);
    }
}
