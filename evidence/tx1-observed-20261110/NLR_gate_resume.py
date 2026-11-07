"""Continue unsubmitted independent audit groups; never replay L122."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
def invoke(a):
 assert not(E/a/'receipt.json').exists(),'Never resubmit'
 return subprocess.run([sys.executable,str(E/'NLR_run.py'),a]).returncode
for n,mode in [(123+j,'proof'+str(15+j))for j in range(15)]+[(138,'close')]:
 a=f'NLR_L{n:03d}';subprocess.run([sys.executable,str(E/'NLR_audit_config.py'),a,mode],check=True)
 rc=invoke(a)
 if mode.startswith('proof'):
  # Preserve actual nonzero known collector disagreements; raw verdict is audited below.
  assert (E/a/'receipt.json').exists()
  checked=json.loads((E/'NLR_audit'/mode/(mode+'.json')).read_text())
  idx=int(mode[5:]);expected=json.loads((E/'NLR_AUDIT_ROOTS.json').read_text())['groups'][idx]
  results=checked['results'];assert sorted(r['root']for r in results)==sorted(expected),(a,'incomplete raw coverage')
  assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results),(a,'nonstandard raw axiom')
  if rc:assert any(not r['equal']for r in results) or (rc==124 and checked['exit_status']==0),(a,'unexpected raw audit failure')
 else:assert rc==0,(a,mode,rc)
print(json.dumps(dict(campaign='COMPLETE_THROUGH_L138',combined_imports=1,final_native_credit=0)),flush=True)
