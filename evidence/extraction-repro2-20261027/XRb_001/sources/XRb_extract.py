from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
old=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
a=old/'XRa_bin/aeneas-b59d5188-extended'
p=old/'XRa_release_candidate_tx1.llbc'
assert hashlib.file_digest(a.open('rb'),'sha256').hexdigest()=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()=='0814e4ec3481bef7fcca9a806ff24c868fdaeae3ed127b1e11a73973077510ba'
cmd=[str(a),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1PublicPreparation','-dest',str(B/'XRb_release_generated'),'-subdir','AspisR1PublicPreparation','-split-files','-emit-json',str(p)]
(B/'XRb_release_command.json').write_text(json.dumps(cmd,indent=2)+'\n')
print('COMMAND',json.dumps(cmd),flush=True)
r=subprocess.run(cmd)
rows=[]
for p in sorted((B/'XRb_release_generated').rglob('*')):
 if p.is_file(): rows.append({'path':str(p),'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size})
(B/'XRb_release_outputs.json').write_text(json.dumps({'exit':r.returncode,'outputs':rows},indent=2)+'\n')
print(json.dumps(rows),flush=True)
raise SystemExit(r.returncode)
