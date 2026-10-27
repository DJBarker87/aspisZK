from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
a=O/'XRa_bin/aeneas-b59d5188-extended'
assert hashlib.file_digest(a.open('rb'),'sha256').hexdigest()=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
p=B/'XRf_closed_release_candidate_tx1.llbc'
r=json.loads((B/'XRf_closed_release_candidate_charon_result.json').read_text())
v=json.loads((B/'XRf_closed_release_candidate_tx1_inventory.json').read_text())
assert v['ready_for_aeneas'] and len(v['release_opaque'])==6
assert v['sha256']==r['llbc_sha256']
assert r['exit']==0 and r['llbc_has_errors'] is False
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==r['llbc_sha256']
cmd=[str(a),'-log','Translate','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','XRf_Release','-dest',str(B/'XRf_generated'),'-subdir','XRf_Release','-split-files','-emit-json',str(p)]
(B/'XRf_aeneas_command.json').write_text(json.dumps({'command':cmd,'input_llbc_sha256':r['llbc_sha256'],'input_unmodified':True},indent=2)+'\n')
print('COMMAND',json.dumps(cmd),flush=True)
x=subprocess.run(cmd)
rows=[{'path':str(q),'sha256':hashlib.file_digest(q.open('rb'),'sha256').hexdigest(),'bytes':q.stat().st_size} for q in sorted((B/'XRf_generated').rglob('*')) if q.is_file()]
(B/'XRf_outputs.json').write_text(json.dumps({'exit':x.returncode,'outputs':rows},indent=2)+'\n')
print(json.dumps(rows),flush=True)
raise SystemExit(x.returncode)
