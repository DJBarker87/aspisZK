"""Focused cache/source preflight; read-only, invokes no Lean process."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
base='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
cfg=json.loads((P/'JGr24_099.json').read_text())
valid={}
for rp in P.glob('JGr24_*/receipt.json'):
 d=json.loads(rp.read_text())
 if d['exit_status']==0:valid.update(d['source_hashes'])
own={}
for f in sorted((R/'lean').glob('JGr_*.lean')):
 if f.stem=='JGr_FinalAudit':continue
 h=hashlib.sha256(f.read_bytes()).hexdigest()
 assert valid.get(f.name)==h,('No passing current source',f)
 own[f.stem]=h
inherited=json.loads((R/'evidence/joint-fixture23-20261027/JGp_FINAL_CLOSURE_PREFLIGHT.json').read_text())['selection']
payload=dict(base=base,paths=cfg['env']['LEAN_PATH'].split(':'),own=own,inherited=inherited,
 extras=['JGp_FinalAudit','JGm_TX2_Batch','FJu_Top'])
script='''from pathlib import Path
import json,hashlib
x=json.loads(PAYLOAD)
selection={}
for m in dict.fromkeys([*x['own'],*x['inherited'],*x['extras']]):
 p=next((Path(root)/(m+'.olean') for root in x['paths'] if (Path(root)/(m+'.olean')).is_file()),None)
 assert p is not None,('missing object',m)
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if m in x['inherited']:assert sha==x['inherited'][m]['object_sha256'],('inherited object changed',m)
 source=Path(x['base'])/(m+'.lean')
 source_hash=hashlib.sha256(source.read_bytes()).hexdigest() if source.exists() else None
 if m in x['own']:assert source_hash==x['own'][m],('own host source mismatch',m)
 selection[m]=dict(object=str(p),object_sha256=sha,bytes=p.stat().st_size,source_sha256=source_hash)
print(json.dumps(dict(classification='Focused cached-object/source inventory, not a fresh frozen release replay',selection=selection,own_sources=len(x['own']),inherited_jgp=len(x['inherited']),missing=[],d18_before_aspis=x['paths'].index('/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects')<x['paths'].index('/home/dombarker/project-offloads/aspis-joint-20261019/objects')),indent=2))
'''.replace('PAYLOAD',repr(json.dumps(payload)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=script,capture_output=True,text=True)
(P/'JGr_CLOSURE_PREFLIGHT.log').write_text(r.stderr)
assert r.returncode==0,(r.returncode,r.stderr)
d=json.loads(r.stdout);assert d['d18_before_aspis']
(P/'JGr_FINAL_CLOSURE_PREFLIGHT.json').write_text(r.stdout)
print('closure preflight:',len(d['selection']),'objects,',d['own_sources'],'own source hashes, no missing object')
