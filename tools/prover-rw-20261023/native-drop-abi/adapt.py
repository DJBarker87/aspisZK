"""Import relocation and removal of generated limits only; never edit terms."""
from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
E=H/'native-drop-abi'
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z')
rows=[]
for attempt,kind in [(36,'NoDrop'),(42,'Guard')]:
 for part in ['Types','Funs']:
  p=E/f'extraction{attempt:03d}/raw-output/{part}.lean'; raw=p.read_text(); s=raw
  # Match exactly the two known generator comment/option blocks.
  s=re.sub(r'/\- You can set the `maxHeartbeats`[^\n]*\nset_option maxHeartbeats 1000000\n\n','',s)
  s=re.sub(r'/\- You can set the `maxRecDepth`[^\n]*\nset_option maxRecDepth 2048\n\n','',s)
  if part=='Funs':s=s.replace('import ProverRwNativeEntropyDropV5.Types',f'import R1Z.ProverRwNativeDropABI{kind}Types').replace('import ProverRwNativeDropNoDrop.Types',f'import R1Z.ProverRwNativeDropABI{kind}Types')
  assert 'set_option max' not in s
  out=J/f'ProverRwNativeDropABI{kind}{part}.lean'
  assert not out.exists(), str(out)
  out.write_text(s)
  rows.append(dict(raw_path=str(p),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),adapted_path=str(out),adapted_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='Remove two generated limit blocks; rewrite split Types import only. No declaration/type/body change.',accepted_artifact=False))
(E/'adaptation.json').write_text(json.dumps(rows,indent=2)+'\n')
