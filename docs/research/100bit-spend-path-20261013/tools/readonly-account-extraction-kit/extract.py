#!/usr/bin/env python3
"""Exact private helper cut; SDK definitions are genuine crate dependencies."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent
REV='b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c'
SOURCE='programs/r1-cost-probe/src/r1_pool_adapter.rs'
def sha(b):return hashlib.sha256(b).hexdigest()
raw=subprocess.check_output(['git','show',REV+':'+SOURCE],cwd=P)
lines=raw.decode().splitlines(keepends=True)
a=next(i for i,l in enumerate(lines) if l.startswith('fn require_readonly_account('));b=next(i for i in range(a,len(lines)) if lines[i]=='}\n')
cut=''.join(lines[a:b+1])
text='''#![allow(dead_code)]
// Namespace-only wrapper. These are the exact SDK types reexported by solana_program.
pub mod r1_pool_adapter {
use solana_account_info::AccountInfo;
use solana_pubkey::Pubkey;
use solana_program_error::{ProgramError, ProgramResult};

'''+cut+'}\n'
pins={'source_revision':REV,'source':SOURCE,'source_sha256':sha(raw),'span':[a+1,b+1],'span_sha256':sha(cut.encode()),'exact_declaration':cut,'wrapping':'Private declaration unchanged, including signature/body; namespace-only wrapper and direct imports of actual SDK nominal types. No AccountInfo, Pubkey or ProgramError type replacement.','feature_scope':'Direct SDK features match solana-program2.3 default-borsh dependency feature declarations for these three crates; unused Solana APIs are not roots.','dependencies':{'solana-account-info':'=2.3.0','solana-pubkey':'=2.4.0','solana-program-error':'=2.2.2'},'seed_lock_sha256':sha(subprocess.check_output(['git','show',REV+':Cargo.lock'],cwd=P)),'kit_files':{n:sha((P/n).read_bytes()) for n in ['Cargo.toml','extract.py']}}
pins['kit_files']['lib.rs']=sha(text.encode())
args=argparse.ArgumentParser();args.add_argument('--check',action='store_true');o=args.parse_args()
if o.check:
 assert (P/'lib.rs').read_text()==text
 assert json.loads((P/'source-pins.json').read_text())==pins
 print('PASS: unchanged actual private helper and real SDK imports')
else:
 (P/'lib.rs').write_text(text);(P/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
