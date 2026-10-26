#[cfg(kani)]
pub fn zero_as_mut<T,Z:zeroize::Zeroize+AsMut<T>>(z:&mut zeroize::Zeroizing<Z>)->&mut T { z.as_mut() }
#[cfg(kani)]
pub fn zero_deref_mut<Z:zeroize::Zeroize>(z:&mut zeroize::Zeroizing<Z>)->&mut Z { &mut *z }
#[cfg(kani)]
pub fn ct_update(z:&mut sha2::digest::core_api::CtVariableCoreWrapper<sha2::Sha256VarCore,sha2::digest::typenum::U32>,blocks:&[sha2::digest::core_api::Block<sha2::Sha256VarCore>]) {
    use sha2::digest::core_api::UpdateCore;
    z.update_blocks(blocks)
}
#[cfg(kani)]
pub fn string_new(n:usize)->String { String::with_capacity(n) }
#[cfg(kani)]
pub fn string_push(s:&mut String,t:&str) { s.push_str(t); }
#[cfg(kani)]
pub fn string_path(s:&String)->&std::path::Path { s.as_ref() }
#[cfg(kani)]
pub fn file_flush(file:&mut std::fs::File)->std::io::Result<()> {
    use std::io::Write;
    file.flush()
}

#[cfg(all(kani,not(pdict_extract)))]
#[kani::proof]
fn zeroizing_mutable_adapters_full_frame() {
    #[derive(Clone)]
    struct State { before:u64, cell:u64, after:u64 }
    impl zeroize::Zeroize for State {
        fn zeroize(&mut self) { self.cell=0; }
    }
    impl AsMut<u64> for State {
        fn as_mut(&mut self)->&mut u64 { &mut self.cell }
    }
    let before:u64=kani::any(); let cell:u64=kani::any(); let after:u64=kani::any();
    let replacement:u64=kani::any();
    let mut z=zeroize::Zeroizing::new(State{before,cell,after});
    assert!(*zero_as_mut(&mut z)==cell);
    *zero_as_mut(&mut z)=replacement;
    assert!(zero_deref_mut(&mut z).cell==replacement);
    assert!(z.before==before && z.after==after);
    let next:u64=kani::any();
    zero_deref_mut(&mut z).cell=next;
    assert!(*zero_as_mut(&mut z)==next);
    assert!(z.before==before && z.after==after);
}
#[cfg(kani)]
pub fn ct_default()->sha2::digest::core_api::CtVariableCoreWrapper<sha2::Sha256VarCore,sha2::digest::typenum::U32> { Default::default() }
#[cfg(kani)]
pub fn wrapper_default()->sha2::Sha256 { Default::default() }
#[cfg(kani)]
pub fn wrapper_update(state:&mut sha2::Sha256,data:&[u8]) {
    use sha2::digest::Update;
    Update::update(state,data);
}
#[cfg(kani)]
pub fn wrapper_finalize(state:sha2::Sha256,out:&mut sha2::digest::Output<sha2::Sha256>) {
    use sha2::digest::FixedOutput;
    state.finalize_into(out);
}
#[cfg(kani)]
pub fn io_kind(error:&std::io::Error)->std::io::ErrorKind { error.kind() }
#[cfg(kani)]
pub fn option_some_and(value:Option<u64>,f:impl FnOnce(u64)->bool)->bool { value.is_some_and(f) }
#[cfg(kani)]
pub fn option_ref(value:&Option<u64>)->Option<&u64> { value.as_ref() }
#[cfg(kani)]
pub fn option_or(value:Option<u64>,error:u32)->Result<u64,u32> { value.ok_or(error) }
#[cfg(kani)]
pub fn option_eq(left:Option<u64>,right:Option<u64>)->bool { left==right }
#[cfg(kani)]
pub fn option_try(value:Option<u64>)->Option<u64> { Some(value?) }
#[cfg(kani)]
pub fn result_map(value:Result<u64,u32>,f:impl FnOnce(u64)->u64)->Result<u64,u32> { value.map(f) }
