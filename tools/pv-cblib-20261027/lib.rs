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
