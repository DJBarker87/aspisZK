#!/usr/bin/env python3
"""Validate the default selection, and bind it to S4 without rerunning CU."""
import hashlib,json,subprocess
from pathlib import Path
out=Path('results/r0-e2e-20261009/re4')
def run(label,*cmd):subprocess.run(['python3','scripts/r0_re4_run.py',label,*cmd],check=True)
run('selected-native','cargo','test','--release','--locked','-p','aspis-prover','--features','r0,insecure-spend-fixture,r0-e4-reference','--test','r0_e2e','--','--nocapture','--include-ignored')
run('selected-sbf','cargo','build-sbf','--manifest-path','programs/aspis-verifier/Cargo.toml','--sbf-out-dir',str(out/'selected-elf'),'--no-default-features','--features','r0-cu-probe','--','--locked','-j','2')
run('selected-stack','python3','scripts/r0_re3_stack_audit.py',str(out/'selected-sbf.log'),'/home/dombarker/project-offloads/aspis-r0-semantics-20261009/target/sbpf-solana-solana/release/aspis_verifier.so',str(out/'selected-elf/aspis_verifier.so'),str(out/'selected-stack'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=out/'s4-stack/linked.text';b=out/'selected-stack/linked.text'
record={'s4_text_sha256':sha(a),'selected_text_sha256':sha(b),'text_byte_identical':a.read_bytes()==b.read_bytes(),'s4_elf_sha256':sha(out/'s4-elf/aspis_verifier.so'),'selected_elf_sha256':sha(out/'selected-elf/aspis_verifier.so'),'measurements_reused':'s4; no unchanged CU rerun'}
(out/'selected-artifact-equality.json').write_text(json.dumps(record,indent=2)+'\n')
assert record['text_byte_identical'], 'selected executable text differs; do not silently reuse measurement'
