#!/usr/bin/env python3
"""Verify original production source is unchanged and pin task inputs."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/asq8-kani-20261021'
BASE='8138bc818'
sha=lambda b:hashlib.sha256(b).hexdigest()
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
s=(R/path).read_text()
a=s.index('#[cfg(any(test, kani, aeneas_ref))]\n#[path = "asq8_payment_reference.rs"]')
b=s.index('pub fn decode_pool_v1_pair_forest_terminal_request_v1(',a)
original=subprocess.check_output(['git','show',f'{BASE}:{path}'],cwd=R)
assert (s[:a]+s[b:]).encode()==original, 'pre-existing statement source changed'
changed=subprocess.check_output(['git','diff','--name-only',BASE,'--','programs','crates'],cwd=R,text=True).splitlines()
allowed={path,'crates/aspis-statement/src/pool_v1/asq8_kani.rs','crates/aspis-statement/src/pool_v1/asq8_payment_reference.rs'}
assert set(changed)<=allowed, changed
files=subprocess.check_output(['git','ls-files','.cargo','crates','programs','Cargo.toml','Cargo.lock','rust-toolchain.toml','docs/research/v8-r0-zk-20261009/refine'],cwd=R,text=True).splitlines()
inputs={p:sha((R/p).read_bytes()) for p in files if (R/p).is_file()}
(E/'source-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
(E/'source-binding.json').write_text(json.dumps(dict(base=BASE,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),existing_terminal_source_unchanged=True,original_terminal_sha256=sha(original),gated_addition_sha256=sha(s[a:b].encode()),changed_rust_files=changed,production_pool_and_verifier_unchanged=True),indent=2)+'\n')
print(f'{len(inputs)} host inputs pinned; all existing statement, Pool and verifier source unchanged')
