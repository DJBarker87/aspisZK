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
