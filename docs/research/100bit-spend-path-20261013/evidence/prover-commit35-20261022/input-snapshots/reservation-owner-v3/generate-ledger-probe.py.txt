#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent;H=E/'ledger-probe';H.mkdir(exist_ok=True)
s=Path('crates/aspis-prover/src/state_only_entropy.rs').read_text()
a=s.index('pub struct DurableStateOnlyMaskNonceStore');b=s.index('\n#[cfg(test)]\nmod tests',a)
body=s[a:b]
header='''use std::{fs::{self,File,OpenOptions},io::{self,Write},path::{Path,PathBuf}};
use std::os::unix::fs::OpenOptionsExt;
use sha2::{Digest,Sha256};
const ATTEMPT_RESERVATION_DOMAIN: &[u8] = b"aspis:state-only:attempt-reservation:v1";
const RESERVATION_MAGIC: &[u8; 16] = b"ASPIS-MASK-V1\\0\\0\\0";
pub trait StateOnlyMaskNonceStore {fn reserve(&mut self,statement_digest:[u8;32],mask_nonce:[u8;32])->bool;}
'''
main='''
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
    println!("{{\\"duplicate\\":{},\\"fresh\\":{},\\"same_prior_status_history\\":true,\\"old_path\\":\\"{}\\",\\"fresh_path\\":\\"{}\\",\\"files_retained\\":true}}",duplicate,new,p.display(),q.display());
    Ok(())
}
'''
(H/'main.rs').write_text(header+body+main)
(H/'Cargo.toml').write_text('[package]\nname="aspis-ledger-probe35"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[[bin]]\nname="ledger-probe35"\npath="main.rs"\n[dependencies]\nsha2="=0.10.9"\n')
(E/'ledger-probe-source-pins.json').write_text(json.dumps(dict(source_path='crates/aspis-prover/src/state_only_entropy.rs',source_sha256=hashlib.sha256(s.encode()).hexdigest(),verbatim_store_and_sync_sha256=hashlib.sha256(body.encode()).hexdigest(),native_std_and_sha2=True,secret_values='none: fixed public test nonces only',cleanup='all host test ledger entries retained'),indent=2)+'\n')
