from common import *
s=std('std/src/path.rs');st=std('alloc/src/string.rs');ref=(R/'tools/pv-cblib-20261027/lib.rs').read_text();native=(R/'tools/pv-relink-20261028/v179.rs').read_text()
a=s[s.index('AsRef<Path> for String'):];checks=[checked(a,'fn as_ref(', '{Path::new(self)}'),checked(s,'pub const fn new<S:', '{unsafe {&*(s.as_ref() as *const OsStr as *const Path)}}')]
checks.append(checked(native,'fn string_owned_reference(',body(ref,'fn string_owned_reference(')))
os=(E/'stdlib/std/src/ffi-os_str.rs.txt').read_text()
checks.extend([
 checked(os[os.index('AsRef<OsStr> for String'):],'fn as_ref(', '{(&**self).as_ref()}'),
 checked(os[os.index('AsRef<OsStr> for str'):],'fn as_ref(', '{OsStr::from_inner(Slice::from_str(self))}'),
 checked(os,'pub fn as_encoded_bytes(', '{self.inner.as_encoded_bytes()}')])
checks.append(dict(os_str_file_sha256=sha(os.encode()),pin='nightly-2026-06-01 rust-src; full retained source',borrow_chain=['String::as_ref<Path>','Path::new','String::as_ref<OsStr>','String deref str','str::as_ref<OsStr>','Unix Slice::from_str; transparent views']))
checks.append(dict(reference_body=body(ref,'fn string_owned_reference('),reference_path='tools/pv-cblib-20261027/lib.rs',path_file_sha256=sha(s.encode()),string_file_sha256=sha(st.encode())))
report('V179',checks,[{'difference':'Borrowed Path reinterpretation vs owned String identity. Neither changes bytes; all byte observers agree. Lifetime/representation/compiler refinement stays explicit.','proof':'PV_RL_V179.observer; PV_CBL_StringViewValue.total'}, {'difference':'String -> str -> OsStr -> encoded bytes are borrowed native views; reference carrier String represents the same valid UTF8.','proof':'PV_RL_V179.complete; domain is valid native String, not arbitrary invalid bytes'}],['PV_CBL_StringViewSource.op28_source','PV_CBL_StringViewValue.total','PV_RL_V179.complete'],'PV_RL_V179.nonvacuous; native run enumerates Unicode scalars and empty/context strings')
