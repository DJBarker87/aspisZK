use std::{fs::{self,File,OpenOptions},io::{self,Write},path::{Path,PathBuf}};
use std::os::unix::fs::OpenOptionsExt;
use sha2::{Digest,Sha256};
const ATTEMPT_RESERVATION_DOMAIN: &[u8] = b"aspis:state-only:attempt-reservation:v1";
const RESERVATION_MAGIC: &[u8; 16] = b"ASPIS-MASK-V1\0\0\0";
pub trait StateOnlyMaskNonceStore {fn reserve(&mut self,statement_digest:[u8;32],mask_nonce:[u8;32])->bool;}
pub struct DurableStateOnlyMaskNonceStore {
    directory: PathBuf,
    last_error: Option<io::ErrorKind>,
}

impl DurableStateOnlyMaskNonceStore {
    pub fn open(directory: impl AsRef<Path>) -> io::Result<Self> {
        fs::create_dir_all(directory.as_ref())?;
        let metadata = fs::metadata(directory.as_ref())?;
        if !metadata.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotADirectory,
                "mask nonce ledger path is not a directory",
            ));
        }
        Ok(Self {
            directory: directory.as_ref().to_path_buf(),
            last_error: None,
        })
    }

    pub fn last_error(&self) -> Option<io::ErrorKind> {
        self.last_error
    }

    fn reservation_path(&self, mask_nonce: &[u8; 32]) -> PathBuf {
        // The nonce is burned globally within this wallet ledger, even if a
        // caller tries to reuse it under a different statement digest.
        let mut hasher = Sha256::new();
        hasher.update(ATTEMPT_RESERVATION_DOMAIN);
        hasher.update(mask_nonce);
        let digest: [u8; 32] = hasher.finalize().into();
        let mut name = String::with_capacity(69);
        for byte in digest {
            use std::fmt::Write as _;
            write!(&mut name, "{byte:02x}").expect("writing to String cannot fail");
        }
        name.push_str(".burn");
        self.directory.join(name)
    }

    pub fn reserve_fallible(
        &mut self,
        statement_digest: [u8; 32],
        mask_nonce: [u8; 32],
    ) -> io::Result<bool> {
        self.last_error = None;
        let path = self.reservation_path(&mask_nonce);
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

impl StateOnlyMaskNonceStore for DurableStateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        match self.reserve_fallible(statement_digest, mask_nonce) {
            Ok(reserved) => reserved,
            Err(error) => {
                self.last_error = Some(error.kind());
                false
            }
        }
    }
}

#[cfg(unix)]
fn sync_directory(directory: &Path) -> io::Result<()> {
    File::open(directory)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_directory: &Path) -> io::Result<()> {
    // `create_new` remains atomic. Platforms without directory-fsync support
    // must place this ledger on a storage layer whose metadata is durable.
    Ok(())
}

fn main()->io::Result<()> {
    let root=PathBuf::from(std::env::args().nth(1).expect("explicit retained evidence directory"));
    // Public fixed test nonces, never wallet/account keys. Retain all files.
    let mut store=DurableStateOnlyMaskNonceStore::open(root)?;
    let old=[1u8;32];let fresh=[2u8;32];
    let p=store.reservation_path(&old);let q=store.reservation_path(&fresh);
    assert_ne!(p,q);
    assert_eq!(store.reserve_fallible([3;32],old)?,true);
    // Both hypothetical next calls begin with this same ledger. Each prior
    // RNG result is Ok, with no zero-block retry. Only the nonce differs.
    let duplicate=store.reserve_fallible([3;32],old)?;
    let new=store.reserve_fallible([3;32],fresh)?;
    assert!(!duplicate);assert!(new);
    println!("{{\"duplicate\":{},\"fresh\":{},\"same_prior_status_history\":true,\"old_path\":\"{}\",\"fresh_path\":\"{}\",\"files_retained\":true}}",duplicate,new,p.display(),q.display());
    Ok(())
}
