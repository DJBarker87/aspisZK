#[cfg(kani)]
pub fn sha_new(size:usize)->Result<sha2::Sha256VarCore,sha2::digest::InvalidOutputSize> {
    use sha2::digest::core_api::VariableOutputCore;
    sha2::Sha256VarCore::new(size)
}
#[cfg(kani)]
pub fn path_as_ref(path:&std::path::Path)->&std::path::Path { path.as_ref() }
#[cfg(kani)]
pub fn pathbuf_as_path(path:&std::path::PathBuf)->&std::path::Path { path.as_path() }
