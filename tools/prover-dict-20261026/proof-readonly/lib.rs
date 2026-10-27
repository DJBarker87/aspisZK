#[cfg(kani)]
pub fn sha_new(size:usize)->Result<sha2::Sha256VarCore,sha2::digest::InvalidOutputSize> {
    use sha2::digest::core_api::VariableOutputCore;
    sha2::Sha256VarCore::new(size)
}
#[cfg(kani)]
pub fn path_as_ref(path:&std::path::Path)->&std::path::Path { path.as_ref() }
#[cfg(kani)]
pub fn pathbuf_as_path(path:&std::path::PathBuf)->&std::path::Path { path.as_path() }
#[cfg(kani)]
pub fn digest_new() -> sha2::Sha256 {
    use sha2::Digest;
    sha2::Sha256::new()
}
#[cfg(kani)]
pub fn error_kind_eq(a: std::io::ErrorKind, b: std::io::ErrorKind) -> bool { a == b }
#[cfg(kani)]
pub fn digest_update(state: &mut sha2::Sha256, data: &[u8]) {
    use sha2::Digest;
    state.update(data)
}
#[cfg(kani)]
pub fn digest_finalize(state: sha2::Sha256) -> [u8; 32] {
    use sha2::Digest;
    state.finalize().into()
}
#[cfg(kani)]
pub fn file_flush(file: &mut std::fs::File) -> std::io::Result<()> {
    use std::io::Write;
    file.flush()
}
