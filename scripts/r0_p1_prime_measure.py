#!/usr/bin/env python3
"""Run a once-only cumulative stage, only after its equality and stack gates."""
import hashlib, json, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-cost-probe-20261009'
stage=sys.argv[1]
for job in ['native','sbf','stack']:
    assert json.loads((out/f'{stage}-{job}.json').read_text())['exit_status']==0, job
assert not json.loads((out/f'{stage}-stack/stack-audit.json').read_text())['reachable_diagnostics']
driver=Path('/home/dombarker/project-offloads/aspis-r0-semantics-20261009/target/release/r0-p1-prime-cu-probe')
plan={'stage':stage,'expected_time':'SBF verifier execution, primarily the V2 structured transpose and dual-fold dot; no compilation or proof generation', 'acceptance':{'per_fixture':5,'limit':1400000},'diagnostic':{'per_fixture':1,'limit':200000000,'label':'DIAGNOSTIC; no acceptance claim'},'caps':{'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':0},'driver_sha256':hashlib.sha256(driver.read_bytes()).hexdigest(),'driver_source':'B cost-probe optimized driver; expanded log capacity only'}
planpath=out/f'{stage}-measurement-plan.json'
assert not planpath.exists()
planpath.write_text(json.dumps(plan,indent=2)+'\n')
for mode,folder in [('measure','acceptance'),('diagnostic','diagnostic')]:
    for fixture in ['transfer','withdrawal']:
        subprocess.run([sys.executable,'scripts/r0_p1_prime_run.py',f'{stage}-{folder}-{fixture}',str(driver),mode,str(out/f'{stage}-elf/aspis_verifier.so'),str(out/'fixtures'),str(out/f'{stage}-{folder}'),fixture],cwd=root,check=True)
