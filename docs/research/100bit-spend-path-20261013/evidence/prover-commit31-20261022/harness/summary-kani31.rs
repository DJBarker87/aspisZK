#[cfg(kani)]
mod summary_kani31 {
    use super::*;
    static mut KEY:[u8;2]=[0;2];static mut VALUE:[u8;32]=[0;32];
    static mut OLD:Option<[u8;32]>=None;static mut CALLS:usize=0;
    // TrustedStd summary of exactly one insertion's observable call/result.
    // Table mutation is supplied by the separately stated standard map law.
    fn insert(_table:&mut Table,key:Vec<u8>,value:[u8;32])->Option<[u8;32]> {unsafe {
        assert_eq!(key.len(),2);assert_eq!(key[0],KEY[0]);assert_eq!(key[1],KEY[1]);
        let byte:usize=kani::any();kani::assume(byte<32);assert_eq!(value[byte],VALUE[byte]);
        CALLS+=1;OLD
    }}
    #[kani::proof] #[kani::unwind(34)]
    #[kani::stub(BTreeMap::<Vec<u8>,[u8;32]>::insert,insert)]
    fn insertion_context() {
        let key:[u8;2]=kani::any();let value:[u8;32]=kani::any();
        let old=if kani::any() {Some(kani::any::<[u8;32]>())} else {None};
        unsafe {KEY=key;VALUE=value;OLD=old;CALLS=0;}
        let mut native=Table::new();let mut bad=false;
        if let Some(previous)=native.insert(key.to_vec(),value) {if previous!=value {bad=true;}}
        unsafe {assert_eq!(CALLS,1);CALLS=0;}
        let (_,actual_bad)=owned31::merge_step(Table::new(),key.to_vec(),value);
        unsafe {assert_eq!(CALLS,1);}
        assert_eq!(actual_bad,bad);
    }
}
