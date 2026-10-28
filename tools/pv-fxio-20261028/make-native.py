"""Pin the reached store body; the only adaptation is a caller-supplied path.
No body edit, mock I/O, Kani stub, or assumption of write/sync success.
"""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-fxio-20261028'
p=R/'crates/aspis-prover/src/state_only_entropy.rs'; s=p.read_text()
a=s.index('        let mut options = OpenOptions::new();',s.index('    pub fn reserve_fallible('))
b=s.index('\n        Ok(true)',a)+len('\n        Ok(true)')
body=s[a:b]
assert body.count('options.open(path)')==1
assert body.count('file.write_all(')==3
assert body.count('file.sync_all()?')==1
assert body.count('sync_directory(&self.directory)?')==1
# Preserve the exact remaining function body; path computation occurs before
# the selected boundary and is identical for a repeated nonce.
header='''use std::{fs::{self, File, OpenOptions},io::{self,Write},path::{Path,PathBuf}};
use std::os::unix::fs::OpenOptionsExt;
const RESERVATION_MAGIC: &[u8;16] = b"ASPIS-MASK-V1\\0\\0\\0";
struct Store { directory: PathBuf }
fn sync_directory(directory: &Path) -> io::Result<()> {
    File::open(directory)?.sync_all()
}
impl Store {
    fn reached_suffix(&mut self, path: PathBuf, statement_digest:[u8;32],mask_nonce:[u8;32]) -> io::Result<bool> {
'''
main='''
    }
}
fn main() {
 let directory=PathBuf::from(std::env::args_os().nth(1).expect("private fixture directory"));
 fs::create_dir(&directory).unwrap();
 let path=directory.join("same-nonce.burn");
 let mut store=Store { directory:directory.clone() };
 let nonce=[0x42;32]; let digest=[0x73;32];
 assert!(!path.exists());
 let first=store.reached_suffix(path.clone(),digest,nonce).unwrap();
 let after_first=fs::read(&path).unwrap();
 let second=store.reached_suffix(path.clone(),digest,nonce).unwrap();
 let after_second=fs::read(&path).unwrap();
 assert!(first); assert!(!second); assert_eq!(after_first,after_second);
 assert_eq!(after_first.len(),80);
 let e=OpenOptions::new().write(true).create_new(true).mode(0o600).open(&path).unwrap_err();
 assert_eq!(e.kind(),io::ErrorKind::AlreadyExists);
 println!("{{\\"evidence_class\\":\\"finite validation\\",\\"first_reserve\\":true,\\"second_reserve\\":false,\\"same_path\\":true,\\"same_options\\":true,\\"same_digest\\":true,\\"same_nonce\\":true,\\"error_kind\\":\\"AlreadyExists\\",\\"raw_os_error\\":{:?},\\"contents_bytes\\":80,\\"contents_unchanged_on_repeat\\":true,\\"path\\":\\"{}\\",\\"crash_durability_tested\\":false}}",e.raw_os_error(),path.display());
}
'''
out=R/'tools/pv-fxio-20261028/native-repeat.rs';out.write_text(header+body+main)
(E/'native-source-binding.json').write_text(json.dumps(dict(
 source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
 native_path=str(out.relative_to(R)),native_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
 copied_body_sha256=hashlib.sha256(body.encode()).hexdigest(),
 exact_body=body,adaptations=['Caller supplies already computed reservation_path; path hashing is not tested or claimed.','Only self.directory is needed by the verbatim reached suffix; last_error reset precedes it.'],
 scope='verbatim shipped reserve_fallible suffix including all open/write/sync/error branches; finite repeated same-path validation, not a whole-store refinement'),indent=2)+'\n')
print('generated exact reached suffix:',len(body),'bytes')
