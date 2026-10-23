#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
s=json.loads((p/'source-pins.json').read_text())
for rel,d in s['sources'].items():assert hashlib.sha256((p/d['candidate_file']).read_bytes()).hexdigest()==d['candidate_sha256'],rel
m=json.loads((p/'gate-evidence/FINAL-GATE-SUMMARY.json').read_text())
for name,d in m.items():
 r=d['receipt'];assert r['exit_status']==0 and not r.get('verification_failure'),name
 assert r.get('scope_swap_bytes',0)==0,name
assert 'aspis-core' in m['final-core-math']['receipt']['compiled_packages']
c=m['readonly']['cases'];assert len(c)==15 and sum(x['case']=='control' for x in c)==2
for x in c:
 assert x['passed'] and x['verifier_invoked'] and x['verifier_consumption_log'] and x['expected_phase_afterstate_matched']
 if x['case']=='control':assert x['error'] is None
 else:assert x['error']=='InstructionError(3, InvalidAccountData)' and x['protected_accounts_unchanged']
r=m['readonly']['receipt'];assert r['input_pins']['candidate_elf']['sha256']==s['final_candidate_artifact_sha256']
assert s['final_candidate_artifact_sha256']=='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'
assert m['readonly']['comparison']['checkpoint_equal'] and m['readonly']['comparison']['asr8_equal']
print('Four candidate source pins, accepted native gates, explicit final Core compile and final f8 13-rejection/2-control runtime checks verified.')
