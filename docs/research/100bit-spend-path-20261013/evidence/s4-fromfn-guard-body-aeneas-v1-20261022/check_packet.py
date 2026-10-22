#!/usr/bin/env python3
"""Check exact selected LLBC, candidate transform, and Aeneas failure receipt."""
import hashlib, json
from pathlib import Path
R=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
A=R/'attempts'
assert sha(A/'selected-input.llbc')=='170490594c9ee2b994fd59b33062f439c2d1f90f2c12241b8e1a71d57b4eb8a4'
assert sha(A/'input.llbc')==sha(A/'selected-input.llbc')
assert sha(A/'output.llbc')=='47921fa66c7649fb7da70ed9450429ee2b48f709905ed72af63965203622b876'
tr=json.loads((A/'transform-receipt.json').read_text())
assert tr['input_sha256']==sha(A/'input.llbc') and tr['output_sha256']==sha(A/'output.llbc')
run=A/'run-aeneas-v1'
rec=json.loads((run/'receipt.json').read_text())
admit=json.loads((run/'admission-registered.json').read_text())
assert rec['exit_status']==2 and rec['docker_exit_status']==2 and rec['timed_out'] is False
assert rec['input_sha256']==sha(A/'output.llbc')
assert rec['candidate_binary_sha256']=='8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9'
assert rec['max_rss_kib']==79024
assert rec['caps']=={'memory.high':'1073741824','memory.max':'2147483648','memory.swap.max':'0'}
assert rec['proc_cgroup_at_start'].strip()==f"0::{admit['cgroup']}"
assert admit['gate_released_after_all_limit_checks'] is True and admit['verified_limits']==rec['caps']
log=(run/'stdout.log').read_text()
assert 'Could not match the contexts' in log and 'InterpJoin.ml, line 2209' in log
assert 'array_mut = ⊥' in log and 'MB@11' in log
assert not any(p.suffix in {'.lean','.olean','.ilean'} for p in run.rglob('*') if p.is_file())
assert not any(q.suffix in {'.pyc','.so','.o','.bin','.olean','.ilean'} for q in R.rglob('*') if q.is_file()), 'source-only packet'
print('exact selector, guarded transform and bounded Aeneas loop-join failure PASS; no Lean output claimed')
