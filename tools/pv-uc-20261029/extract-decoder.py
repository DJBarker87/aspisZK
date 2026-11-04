"""Focused extraction of the unchanged final decoder for an executable D188 check."""
from pathlib import Path
import json,hashlib,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');x=json.loads((H/'charon.json').read_text());c=x['command'];p=H/'PV_UC_Decoder.llbc'
c[c.index('--start-from')+1]='crate::wallet::decode_wallet_record';c[c.index('--dest-file')+1]=str(p)
B=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2');assert hashlib.sha256(B.read_bytes()).hexdigest()=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
r=subprocess.run(c,cwd=x['cwd']);assert r.returncode==0;assert json.loads(p.read_text())['has_errors'] is False
O=H/'decoder-extraction';O.mkdir(exist_ok=False)
a=[str(B),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_UC_Decoder','-dest',str(O),'-split-files','-emit-json',str(p)]
r=subprocess.run(a)
(O/'receipt.json').write_text(json.dumps(dict(charon_command=c,aeneas_command=a,llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),outputs={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in O.glob('*.lean')},exit=r.returncode),indent=2)+'\n');raise SystemExit(r.returncode)
