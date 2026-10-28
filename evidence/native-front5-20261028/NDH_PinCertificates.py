"""Pin reference identities and the admitted inherited integer gates."""
from pathlib import Path
import json,hashlib,re
from NDH_patch import read_input
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def newfiles(patch):
 out={};name=None;fresh=False
 for l in patch.splitlines(True):
  if l.startswith('--- '):fresh=l.startswith('--- /dev/null');name=None
  elif l.startswith('+++ b/'):
   name=l[6:].strip() if fresh else None
   if name is not None:out[name]=''
  elif name is not None and l.startswith('+'):out[name]+=l[1:]
 return out
pins={}
for n,k in [(1,10),(2,55),(3,74)]:
 a=f'NDH_E{n:03}';logs=(E/a/'stdout.log').read_text()
 p=next(json.loads(l) for l in logs.splitlines() if l.startswith('{') and 'charon_sha256' in l)
 files=newfiles((E/f'NDH_K{k:03}'/'NDH_harness.patch').read_text())
 src=files['crates/aspis-r1-cost-probe/src/NDH_reference.rs']
 assert sha(src.encode())==p['rust_reference_sha256'],(a,'reference hash drift')
 p['source_reconstruction']=f'evidence/native-front5-20261028/NDH_K{k:03}/NDH_harness.patch:crates/aspis-r1-cost-probe/src/NDH_reference.rs'
 (E/a/'NDH_EXTRACTION_PINS.json').write_text(json.dumps(p,indent=2)+'\n');pins[a]=p
p=json.loads((E/'NDH_E004/NDH_EXTRACTION_PINS.json').read_text())
assert sha(read_input('NDH_transcript_reference.rs').encode())==p['rust_reference_sha256'];pins['NDH_E004']=p
p=json.loads((E/'NDH_E005/NDH_EXTRACTION_PINS.json').read_text());assert sha(read_input('NDH_registry_reference.rs').encode())==p['rust_reference_sha256'];pins['NDH_E005']=p
(E/'NDH_EXTRACTION_HISTORY.json').write_text(json.dumps(pins,indent=2)+'\n')
used=[];old=R/'evidence/leaf-sampler1-20261027'
tools=json.loads((E/'NDH_TOOLCHAIN.json').read_text())['tools']
for line in (old/'LPk_TOOLCHAIN.log').read_text().splitlines():
 if len(line.split())==2 and line.split()[1] in tools:
  assert tools[line.split()[1]]['sha256']==line.split()[0]
for n in [8,9,20]:
 a=f'LPk_K{n:03}';r=json.loads((old/a/'receipt.json').read_text());assert r['exit_status']==0
 graph=json.loads((old/(a+'-graph-check.json')).read_text());assert graph.get('graph_matches_frozen') is True
 lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 for label in ['before','after']:assert (old/(a+'-lock-'+label+'.log')).read_text().split()[0]==lock
 artifacts=[a+'/receipt.json',a+'/LPk_harness.patch',a+'-graph-check.json',a+'-lock-before.log',a+'-lock-after.log']
 used.append(dict(attempt=a,exit_status=0,artifacts={str((old/p).relative_to(R)):sha((old/p).read_bytes()) for p in artifacts},feature_body_identity='The reached harness is scalar rem/limb/P arithmetic only, P=2147483647; no crate/user callee, cfg branch, copy builtin or function pointer is reached. Same compiler/backend hashes as current NDH tools. No old traversal/copy receipt is reused.'))
(E/'NDH_INTEGER_REUSE.json').write_text(json.dumps(dict(gates=used,lean_lift='NDH_Arithmetic; NDH_L047',domain='remainder<P, limb<2^32; quotient<2^32 by K008; remainder<P by K009; K020 sparse word identity, lifted without wrap in NDH_Arithmetic'),indent=2)+'\n')
print('five extraction sources reconstructed; three scalar-only integer gates pinned')
