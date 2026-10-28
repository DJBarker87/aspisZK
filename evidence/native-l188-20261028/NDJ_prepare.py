"""Prepare task-owned copied cache and audit pins; never modifies seed roots."""
import json,hashlib,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parents[1]
B='/home/dombarker/project-offloads/codex-cx-l188-cache-20261028'
def read(p):return json.loads((R/p).read_text())
r=read('evidence/replay-deployed2-20261027/RPx_0038.json')['env']['LEAN_PATH'].split(':')
j=read('evidence/joint-sha453-20261028/JHx_045.json')['env']['LEAN_PATH'].split(':')
graph={}
for l in (R/'evidence/replay-deployed2-20261027/RPx_0038/stdout.log').read_text().splitlines():
 if l.startswith('RPX_IMPORTS '):
  d=json.loads(l[12:]);graph[d['module']]=d['imports']
fallback=read('evidence/joint-agg2-20261028/JHw_SOURCE_IMPORTS.json')
for m,v in read('evidence/sound-int2-20261025/final-closure-manifest.json')['modules'].items():
 fallback.setdefault(m,v)
# Repository source imports supplement the predecessor exact-header graph.
for p in (R/'lean').rglob('*.lean'):
 m=p.relative_to(R/'lean').with_suffix('').as_posix().replace('/','.')
 fallback.setdefault(m,dict(imports=[n for l in p.read_text().splitlines() if l.startswith('import ') for n in l[7:].split()]))
# Historical source headers for object-only aliases; final Lean header audit
# will independently compare these dependency edges.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True,cwd=R).splitlines()
for path in paths:
 if not path.endswith('.lean') or not path.startswith('docs/research/'):continue
 name=Path(path).stem
 if not (name.startswith(('RawCircleSample','AspisR1Poseidon')) or name in ['GammaCandidateTotalityV14','RawPoseidonExternalRows','RawPoseidonRowField']):continue
 if '/evidence/' in path:continue
 text=subprocess.check_output(['git','show','HEAD:'+path],cwd=R,text=True)
 module=('AspisR1CircleSampleWrapper.'+name) if name.startswith('RawCircleSample') else name
 fallback.setdefault(module,dict(imports=['Init']+[n for l in text.splitlines() if l.startswith('import ') for n in l[7:].split()],source_git=path,sha256=hashlib.sha256(text.encode()).hexdigest()))
for part in ['Types','Funs','FunsExternal']:
 path='evidence/native-tx2k-20261028/NBX_imports/AspisR1CircleSampleWrapper/'+part+'.lean'
 try:text=subprocess.check_output(['git','show','HEAD:'+path],cwd=R,text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:continue
 fallback.setdefault('AspisR1CircleSampleWrapper.'+part,dict(imports=['Init']+[n for l in text.splitlines() if l.startswith('import ') for n in l[7:].split()],source_git=path,sha256=hashlib.sha256(text.encode()).hexdigest()))
inputs=dict(base=B,rpx_paths=r,joint_paths=j,graph=graph,fallback=fallback,rpx_pins=read('evidence/replay-deployed2-20261027/RPx_retained-object-pins.json'))
(E/'NDJ_SEED_INPUT.json').write_text(json.dumps(inputs,indent=2)+'\n')
