from pathlib import Path
import json,hashlib,subprocess,sys
B=Path(__file__).resolve().parent;manifest=json.loads((B/'PCD_REQUEST_LLBC_INPUT.json').read_text());llbc=B/'PCD_frozen_request.llbc'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(llbc)==manifest['sha256']
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCD_FrozenRequest','-dest',str(B/'PCD_request_extracted'),'-subdir','PCD_FrozenRequest','-split-files',str(llbc)]
pins=dict(phase='Aeneas ONLY on hash-pinned actual selected structured frozen body',aeneas_sha256=sha(A),llbc_sha256=sha(llbc),command=cmd)
(B/'PCD_REQUEST_AENEAS_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
r=subprocess.run(cmd,cwd=B)
pins.update(exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in (B/'PCD_request_extracted').rglob('*') if p.is_file()})
(B/'PCD_REQUEST_AENEAS_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
sys.exit(r.returncode)
