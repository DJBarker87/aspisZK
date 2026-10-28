from common import *
s=std('std/src/path.rs');u=std('std/src/sys/path/unix.rs');ref=(R/'tools/pv-cblib-20261027/lib.rs').read_text();native=(R/'tools/pv-relink-20261028/v178.rs').read_text()
checks=[checked(s,'pub fn join<P:', '{self._join(path.as_ref())}'),checked(s,'fn _join(', '{let mut buf=self.to_path_buf();buf.push(path);buf}')]
# Full _push body is pinned by its complete token digest, not selected substrings.
b=body(s,'fn _push(')
expected='''{
 let buf = self.inner.as_encoded_bytes();
 let mut need_sep = buf.last().map(|c| !is_sep_byte(*c)).unwrap_or(false);
 let comps = self.components();
 if comps.prefix_len() > 0 && comps.prefix_len() == comps.path.len() && comps.prefix.unwrap().is_drive() {need_sep = false}
 let need_clear = if cfg!(target_os = "cygwin") {path.prefix().is_some()} else {path.is_absolute() || path.prefix().is_some()};
 if need_clear {self.inner.clear();}
 else if comps.prefix_verbatim() && !path.inner.is_empty() {
 let mut buf: Vec<_> = comps.collect();
 for c in path.components() {match c {Component::RootDir => {buf.truncate(1);buf.push(c);}Component::CurDir => (),Component::ParentDir => {if let Some(Component::Normal(_)) = buf.last() {buf.pop();}}_ => buf.push(c),}}
 let mut res = OsString::new();let mut need_sep = false;
 for c in buf {if need_sep && c != Component::RootDir {res.push(MAIN_SEPARATOR_STR);}res.push(c.as_os_str());need_sep = match c {Component::RootDir => false,Component::Prefix(prefix) => {!prefix.parsed.is_drive() && prefix.parsed.len() > 0}_ => true,}}
 self.inner = res;return;
 } else if path.has_root() {let prefix_len=self.components().prefix_remaining();self.inner.truncate(prefix_len);}
 else if need_sep {self.inner.push(MAIN_SEPARATOR_STR);}
 self.inner.push(path);
}'''
checks.append(checked(s,'fn _push(',expected))
rb=body(ref,'fn join_slices_reference(');checks.append(checked(native,'fn join_slices_reference(',rb))
checks.extend([
 checked(s,'pub fn push<P:', '{self._push(path.as_ref())}'),
 checked(s,'pub fn to_path_buf(', '{PathBuf::from(self.inner.to_os_string())}'),
 checked(s,'fn prefix_len(', '{if !HAS_PREFIXES {return 0;}self.prefix.as_ref().map(Prefix::len).unwrap_or(0)}'),
 checked(s,'fn prefix_verbatim(', '{if !HAS_PREFIXES {return false;}self.prefix.as_ref().map(Prefix::is_verbatim).unwrap_or(false)}'),
 checked(u,'pub fn parse_prefix(', '{None}'),
 checked(u,'pub(crate) fn is_absolute(', '{if cfg!(any(unix,target_os = "hermit",target_os = "wasi",target_os = "motor")) {path.has_root()} else {path.has_root() && path.prefix().is_some()}}')])
assert 'pub const HAS_PREFIXES: bool = false;' in u
assert "path_separator_bytes!(b'/');" in u
checks.append(dict(unix_source_sha256=sha(u.encode()),source=u))
checks.append(dict(reference_path='tools/pv-cblib-20261027/lib.rs',reference_body=rb,reference_sha256=sha(rb.encode())))
report('V178',checks,[
 {'difference':'Unix removes Windows/Cygwin branches: prefix absent, verbatim false, has_root iff leading slash; no lexical normalization.','proof':'PV_RL_V178.unix_control'},
 {'difference':'Native clones base before push, then clears it on absolute path; owned reference skips the discarded copy. Same result contents; allocation effects stay residual.','proof':'PV_RL_V178.contents'},
 {'difference':'Raw Unix byte paths vs UTF8 String adapter. Native finite validation includes invalid UTF8, while callback claim retains its original valid UTF8 carrier restriction.','proof':'PV_CBL_JoinAdapter.decode_output; no source-image enlargement'},
 {'difference':'Generic AsRef Result evaluated before join; its failure must propagate unchanged.','proof':'PV_RL_V178.asref_result'}],['PV_CBL_CallbackBundle.op26_source','PV_CBL_JoinAdapter.decode_output','PV_RL_V178.complete'], 'PV_RL_V178.nonvacuous; native corpus covers empty, relative, absolute, slash and non-ASCII cases')
