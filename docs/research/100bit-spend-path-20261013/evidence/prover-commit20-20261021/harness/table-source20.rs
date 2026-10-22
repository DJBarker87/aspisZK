#[cfg(kani)]
mod table_source20 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(4)]
    fn empty_entry() {
        let address:[u8;1]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        let table=RefCell::new((Table::new(),collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
        let (actual,flag)=table.into_inner();
        assert_eq!(observed,answer);
        assert_eq!(flag,collision);
        assert_eq!(actual.get(address.as_slice()),Some(&answer));
        assert_eq!(actual.len(),1);
        core::mem::forget(actual);
    }
    #[kani::proof]
    #[kani::unwind(4)]
    fn overwritten_entry() {
        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        let mut initial=Table::new();initial.insert(address.to_vec(),old);
        let table=RefCell::new((initial,collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
        let (actual,flag)=table.into_inner();
        assert_eq!(observed,answer);
        assert_eq!(flag,collision || old!=answer);
        assert_eq!(actual.get(address.as_slice()),Some(&answer));
        assert_eq!(actual.len(),1);
        core::mem::forget(actual);
    }    #[kani::proof]
    #[kani::unwind(4)]
    fn overwritten_value() {
        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        let mut initial=Table::new();initial.insert(address.to_vec(),old);
        let table=RefCell::new((initial,collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
        let (actual,flag)=table.into_inner();
        assert_eq!(observed,answer);
        assert_eq!(actual.get(address.as_slice()),Some(&answer));
        assert_eq!(actual.len(),1);
        core::mem::forget(actual);
    }    #[kani::proof]
    #[kani::unwind(4)]
    fn overwritten_flag() {
        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        let mut initial=Table::new();initial.insert(address.to_vec(),old);
        let table=RefCell::new((initial,collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
        let (actual,flag)=table.into_inner();
        assert_eq!(flag,collision || old!=answer);
        core::mem::forget(actual);
    }
}
