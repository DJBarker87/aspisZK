// Direct deployed-toolchain std operation; allocator/error branches retained.
pub fn join(base: &std::path::Path, name: String) -> std::path::PathBuf { base.join(name) }
