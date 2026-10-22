#!/usr/bin/env python3
"""Check pinned transformed-input and bounded Aeneas failure evidence."""
import hashlib, json
from pathlib import Path
R=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(R/'attempts/input.llbc') == '7ef231eb2ade39d5eea83143f392f70aa96cc0ed253761176cd8160777530d00'
assert sha(R/'attempts/output.llbc') == '97ca029a1fe528f3dfe7c724e9a5793cf0a74c243917193e8db554cbf4af7772'
tr=json.loads((R/'attempts/transform-receipt.json').read_text())
assert tr['input_sha256']==sha(R/'attempts/input.llbc') and tr['output_sha256']==sha(R/'attempts/output.llbc')
assert (R/'attempts/test_transform.py').is_file()
out=R/'attempts/run-aeneas-v1'
rec=json.loads((out/'receipt.json').read_text())
admit=json.loads((out/'admission-registered.json').read_text())
assert rec['exit_status']==2 and rec['docker_exit_status']==2
assert rec['input_sha256']==sha(R/'attempts/output.llbc')
assert rec['candidate_binary_sha256']=='8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9'
assert rec['max_rss_kib']==70400 and rec['timed_out'] is False
assert rec['caps']=={'memory.high':'1073741824','memory.max':'2147483648','memory.swap.max':'0'}
assert rec['proc_cgroup_at_start'].strip()==f"0::{admit['cgroup']}"
assert admit['container_id']==rec['container_id']
assert admit['gate_released_after_all_limit_checks'] is True
assert admit['verified_limits']==rec['caps']
text=(out/'stdout.log').read_text()
assert 'Unhandled `BuiltinOrAuto` for trait 7' in text and 'Generated_Types.BuiltinPointee' in text
assert not any(p.suffix in {'.lean','.olean','.ilean'} for p in out.rglob('*') if p.is_file())
assert not any(q.suffix in {'.pyc','.so','.o','.bin','.olean','.ilean'} for q in R.rglob('*') if q.is_file()), 'source-only packet'
print('guard-only transformed LLBC and bounded Aeneas failure evidence PASS; no Lean output claimed')
