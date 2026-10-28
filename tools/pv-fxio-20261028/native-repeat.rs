use std::{fs::{self, File, OpenOptions},io::{self,Write},path::{Path,PathBuf}};
use std::os::unix::fs::OpenOptionsExt;
const RESERVATION_MAGIC: &[u8;16] = b"ASPIS-MASK-V1\0\0\0";
struct Store { directory: PathBuf }
fn sync_directory(directory: &Path) -> io::Result<()> {
    File::open(directory)?.sync_all()
}
impl Store {
    fn reached_suffix(&mut self, path: PathBuf, statement_digest:[u8;32],mask_nonce:[u8;32]) -> io::Result<bool> {
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        let mut file = match options.open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error),
        };

        // A partially written file is still a burned nonce. Never remove it
        // on failure.
        file.write_all(RESERVATION_MAGIC)?;
        file.write_all(&statement_digest)?;
        file.write_all(&mask_nonce)?;
        file.sync_all()?;
        sync_directory(&self.directory)?;
        Ok(true)
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
 println!("{{\"evidence_class\":\"finite validation\",\"first_reserve\":true,\"second_reserve\":false,\"same_path\":true,\"same_options\":true,\"same_digest\":true,\"same_nonce\":true,\"error_kind\":\"AlreadyExists\",\"raw_os_error\":{:?},\"contents_bytes\":80,\"contents_unchanged_on_repeat\":true,\"path\":\"{}\",\"crash_durability_tested\":false}}",e.raw_os_error(),path.display());
}
