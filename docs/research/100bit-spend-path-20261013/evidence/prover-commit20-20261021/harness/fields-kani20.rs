#[cfg(kani)]
mod fields_kani20 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(34)]
    fn complete_chunk() {
        let bytes:[u8;32]=kani::any();let row:u8=kani::any();
        assert_eq!(validate_record_fields(row,&bytes),fields20::validate(row,bytes.to_vec(),0));
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn ignored_suffix() {
        let bytes:[u8;31]=kani::any();let row:u8=kani::any();let n:usize=kani::any();
        kani::assume(n<=31);
        assert_eq!(validate_record_fields(row,&bytes[..n]),Ok(()));
    }
}
