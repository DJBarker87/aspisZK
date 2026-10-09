#!/usr/bin/env python3
"""Sequential gates for a new source stage. Any failed gate stops the stage."""
import json, subprocess, sys
from pathlib import Path
stage=sys.argv[1]
out=Path('results/r0-e2e-20261009/re4')
def run(suffix,*args):
    subprocess.run(['python3','scripts/r0_re4_run.py',stage+'-'+suffix,*args],check=True)
if stage in ['s3','s5','s5b','s5c','s5d']:
    run('field','cargo','test','--release','--locked','-p','aspis-core','--features','r0,r0-e4-reference','--test','r0_e4_field','--','--nocapture')
run('native','cargo','test','--release','--locked','-p','aspis-prover','--features','r0,insecure-spend-fixture,r0-e4-reference','--test','r0_e2e','--','--nocapture','--include-ignored')
assert json.loads((out/'fixtures/corruption-cases.json').read_text())==json.loads((out/'re3-corruption-cases.json').read_text())
run('sbf','cargo','build-sbf','--manifest-path','programs/aspis-verifier/Cargo.toml','--sbf-out-dir',str(out/(stage+'-elf')),'--no-default-features','--features','r0-cu-probe','--','--locked','-j','2')
run('stack','python3','scripts/r0_re3_stack_audit.py',str(out/(stage+'-sbf.log')),'/home/dombarker/project-offloads/aspis-r0-semantics-20261009/target/sbpf-solana-solana/release/aspis_verifier.so',str(out/(stage+'-elf/aspis_verifier.so')),str(out/(stage+'-stack')))
subprocess.run(['python3','scripts/r0_re4_measure.py',stage],check=True)
