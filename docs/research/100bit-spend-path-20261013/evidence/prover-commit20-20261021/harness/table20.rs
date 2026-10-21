// A per-entry source branch, isolated from allocation/tree traversal.
// Exactly the ProgramOne post-insert collision update; the previous entry
// is the return value of Table::insert, which remains a library boundary.
#[cfg(kani)]
mod table20 {
    fn source(previous:Option<[u8;32]>,answer:[u8;32],mut collision:bool)->bool {
        if let Some(prev)=previous { if prev!=answer {collision=true;} }
        collision
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn hit_entry() {
        let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        let collision:bool=kani::any();
        assert_eq!(source(Some(old),answer,collision),collision || old!=answer);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn absent_entry() {
        let answer:[u8;32]=kani::any();let collision:bool=kani::any();
        assert_eq!(source(None,answer,collision),collision);
    }
}
