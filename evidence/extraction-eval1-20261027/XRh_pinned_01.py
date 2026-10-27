from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
G=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro7-20261027')
a=O/'XRa_bin/aeneas-b59d5188-extended'
p=G/'XRg_07_release_candidate_tx1.llbc'
assert hashlib.file_digest(a.open('rb'),'sha256').hexdigest()=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()=='a8832dbd36b9987ec7288ab7580040a70b01feea31d647a97deb47b521bb5575'
v=json.loads((G/'XRg_07_release_candidate_tx1_inventory.json').read_text())
assert v['ready_for_aeneas'] and len(v['release_opaque'])==12
cmd=[str(a),'-log','Translate','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','XRh_Release','-dest',str(B/'XRh_pinned_generated_01'),'-subdir','XRh_Release','-split-files','-emit-json',str(p)]
print('COMMAND',json.dumps(cmd),flush=True)
x=subprocess.run(cmd)
rows=[{'path':str(q),'sha256':hashlib.file_digest(q.open('rb'),'sha256').hexdigest(),'bytes':q.stat().st_size} for q in sorted((B/'XRh_pinned_generated_01').rglob('*')) if q.is_file()]
(B/'XRh_pinned_outputs_01.json').write_text(json.dumps({'exit':x.returncode,'outputs':rows},indent=2)+'\n')
raise SystemExit(x.returncode)
