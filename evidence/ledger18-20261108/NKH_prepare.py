from pathlib import Path
import json,re,lzma,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger17-20261108'
specs=[('ledger17-20261108','NKC'),('verifier-weights-20261108','NJZ'),('sampler-transcript-20261108','NKD'),('terminal3-20261108','NJX'),('tx2-native8-20261108','NJU')]
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKH_20261108'
roots=set();expected={};conflicts=[];seeds=[];extras=[];priority=[];pins=[]
for folder,pre in specs:
 p=E.parent/folder;x=json.loads((p/f'{pre}_AUDIT_ROOTS.json').read_text());roots.update(x if isinstance(x,list)else x.get('roots',sum(x.get('groups',[]),[])))
 for l in(p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre,decision='NKC canonical expectation retained; loaded scan must verify'))
  else:expected[m]=v
 x=json.loads((p/f'{pre}_EXPORT.json').read_text());base=next(x[k]for k in['export','directory','export_dir','path']if k in x)
 for r in x['files']:
  src=r.get('retained',r.get('destination',r.get('path')));assert src.startswith(base+'/'),(pre,src)
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=r['sha256'],bytes=r.get('bytes',r.get('size'))))
 paths=x.get('consumer_paths',x.get('LEAN_PATH'))
 if paths is None:paths=json.loads((p/f'{pre}_PATHS.json').read_text())
 if isinstance(paths,str):paths=paths.split(':')
 if pre=='NJX':
  # Preserve NJX's retained internal priority order; NKC canonical forest precedes it.
  for q in paths:
   if q.startswith(base+'/'):priority.append(C+'/NJX_seed/'+q[len(base)+1:])
  extras+=paths
 else:
  priority.append(C+'/'+pre+'_seed');extras+=paths
 for f in p.iterdir():
  if f.is_file()and any(k in f.name for k in['HANDOFF','CLOSED.json','EXPORT.json','AUDIT_ROOTS','EXPECTED_IMPORTS','PHYSICAL','PLAN_STATUS','LEDGER.json.xz','BASELINE_ROWS']):pins.append(dict(path=str(f.relative_to(E.parents[1])),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
roots=sorted(roots);n=30
(E/'NKH_SPECS.json').write_text(json.dumps(specs,indent=1)+'\n')
(E/'NKH_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NKH_AUDIT_MODULES.json').write_text(json.dumps([['NKH_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
(E/'NKH_COMBINED_IMPORT.lean').write_text(''.join(f'import {pre}_COMBINED_IMPORT\n'for _,pre in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NKC_{name}.lean').read_text();t=s.replace('NKC_','NKH_');(E/f'NKH_{name}.lean').write_text(t);(E/f'NKH_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NKC_'+name,tofile='NKH_'+name)))
for p in E.glob('NKH_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
for n,x in [('EXPECTED_CONFLICTS',conflicts),('SEED_INPUTS',seeds),('INPUT_PINS',pins),('PATHS',list(dict.fromkeys(priority+extras)))]: (E/f'NKH_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
for name in['run','batch','pin','setup','queue']:
 s=(P/f'NKC_{name}.py').read_text().replace('NKC_','NKH_').replace('codex-cx-ledger17-20261108','codex-cx-ledger18-20261108')
 if name=='run':s=s.replace("E.parent/'ledger16-20261108/NJW_CLOSURE_PINS.json.xz'","E.parent/'ledger17-20261108/NKC_CLOSURE_PINS.json.xz'")
 (E/f'NKH_{name}.py').write_text(s)
print(json.dumps(dict(stage='prepare',roots=len(roots),seeds=len(seeds),conflicts=len(conflicts),paths=len(priority+extras))))
