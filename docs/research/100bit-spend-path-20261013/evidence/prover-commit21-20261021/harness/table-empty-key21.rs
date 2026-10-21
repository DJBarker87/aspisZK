#[cfg(kani)]
mod table_empty_key21 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(4)]
    fn actual_overwrite_flag() {
        let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        let mut initial=Table::new();initial.insert(Vec::new(),old);
        let table=RefCell::new((initial,collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[]);
        let (actual,flag)=table.into_inner();
        assert_eq!(observed,answer);
        assert_eq!(flag,collision || old!=answer);
        core::mem::forget(actual);
    }
}
