#[cfg(kani)]
mod siminsert19small {
    use super::*;
    #[kani::proof]
    #[kani::unwind(34)]
    fn overwrite() {
        let old_key:[u8;4]=kani::any();let address=old_key;
        let previous:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        let collision:bool=kani::any();
        let mut table=Table::new();table.insert(old_key.to_vec(),previous);
        let table=RefCell::new((table,collision));
        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
        let (expected,conflict)=owned19::insert(vec![(old_key.to_vec(),previous)],0,address.to_vec(),answer,collision);
        let (actual,actual_conflict)=table.into_inner();
        assert_eq!(observed,answer);
        assert_eq!(actual_conflict,conflict);
        assert_eq!(actual.len(),expected.len());
        for (key,value) in expected {assert_eq!(actual.get(&key),Some(&value));}
    }
}
