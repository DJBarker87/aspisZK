pub fn finalize<D: digest::FixedOutput + Default + digest::Update + digest::HashMarker>(d: D) -> digest::Output<D> { digest::Digest::finalize(d) }
pub fn vec_empty(v: &Vec<u8>) -> bool { v.is_empty() }
pub fn vec_default() -> Vec<u8> { Vec::default() }
pub fn vec_pop(v: &mut Vec<u8>) -> Option<u8> { v.pop() }
pub fn vec_array(v: Vec<u8>) -> Result<[u8;32],Vec<u8>> { v.try_into() }
pub fn string_capacity(n: usize) -> String { String::with_capacity(n) }
pub fn string_push(s: &mut String, t: &str) { s.push_str(t) }
pub fn path_deref(p: &std::path::PathBuf) -> &std::path::Path { p }
pub fn path_asref(p: &std::path::PathBuf) -> &std::path::Path { p.as_ref() }
pub fn string_path(p: &String) -> &std::path::Path { p.as_ref() }
pub fn path_join(p: &std::path::Path, q: &std::path::Path) -> std::path::PathBuf { p.join(q) }

// Safe owned references; no library implementation is replaced or stubbed.
pub fn empty_reference<T>(v: &Vec<T>) -> bool { v.len() == 0 }
pub fn default_reference<T>() -> Vec<T> { Vec::new() }
pub fn pop_reference<T>(v: &mut Vec<T>) -> Option<T> {
    if v.len() == 0 { None } else { Some(v.remove(v.len() - 1)) }
}
pub fn sha_update_blocks(c: &mut sha2::Sha256VarCore, b: &[digest::core_api::Block<sha2::Sha256VarCore>]) {
    digest::core_api::UpdateCore::update_blocks(c,b)
}
pub fn sha_finalize_variable(c: &mut sha2::Sha256VarCore, b: &mut digest::core_api::Buffer<sha2::Sha256VarCore>, o: &mut digest::Output<sha2::Sha256VarCore>) {
    digest::core_api::VariableOutputCore::finalize_variable_core(c,b,o)
}
pub fn sha_finalize_into(c: sha2::Sha256, o: &mut digest::Output<sha2::Sha256>) {
    digest::FixedOutput::finalize_into(c,o)
}
pub fn sha_update(c: &mut sha2::Sha256, b: &[u8]) { digest::Update::update(c,b) }
pub fn sha_default() -> sha2::Sha256 { Default::default() }
pub fn sha_finalize_fixed(c: &mut digest::core_api::CtVariableCoreWrapper<sha2::Sha256VarCore, digest::consts::U32, sha2::OidSha256>, b: &mut digest::core_api::Buffer<sha2::Sha256VarCore>, o: &mut digest::Output<sha2::Sha256>) {
    digest::core_api::FixedOutputCore::finalize_fixed_core(c,b,o)
}
// Safe pure conversion kernel. The adapter retains the input on the None branch.
pub fn array_reference<T: Copy, const N: usize>(v: &[T], zero: T) -> Option<[T;N]> {
    if v.len() != N { return None; }
    let mut out = [zero;N];
    let mut i=0;
    while i<N { out[i]=v[i]; i+=1; }
    Some(out)
}
// Owned safe path-byte reference on Unix. No filesystem operation occurs.
pub fn path_bytes_reference(v: Vec<u8>) -> Vec<u8> { v }
// Functional owned pop reference; every item is moved exactly once.
pub fn pop_owned_reference<T>(v: Vec<T>) -> (Option<T>, Vec<T>) {
    let n = v.len(); let mut remaining = Vec::new(); let mut last = None;
    let mut i=0;
    for item in v {
        if i+1 == n { last = Some(item); } else { remaining.push(item); }
        i+=1;
    }
    (last,remaining)
}

// Unix Path::join as a safe owned byte-string operation.
pub fn join_bytes_reference(base: &[u8], path: &[u8]) -> Vec<u8> {
    let mut out=Vec::new();
    let absolute=path.len()>0 && path[0]==b'/';
    if !absolute {
        let mut i=0;
        while i<base.len() { out.push(base[i]); i+=1; }
        if base.len()>0 && base[base.len()-1]!=b'/' { out.push(b'/'); }
    }
    let mut j=0;
    while j<path.len() { out.push(path[j]); j+=1; }
    out
}
