from pathlib import Path
import json,re,lzma,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger16-20261108'
specs=[('ledger16-20261108','NJW'),('batch-merkle-20261108','NJS'),('claims-queryscan-20261108','NJT'),('multiproof4-20261108','NJV'),('tx2-decoders3-20261108','NJY')]
(E/'NKC_SPECS.json').write_text(json.dumps(specs,indent=1)+'\n')
roots=set();expected={};conflicts=[];seeds=[];extra=[];pins=[]
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKC_20261108'
for folder,pre in specs:
 p=E.parent/folder;x=json.loads((p/f'{pre}_AUDIT_ROOTS.json').read_text())
 if isinstance(x,dict):x=x['roots'] if isinstance(x.get('roots'),list) else sum(x.get('groups',[]),[])
 roots.update(x)
 for l in(p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];xs=x['imports']
  if m in expected and expected[m]!=xs:conflicts.append(dict(module=m,earlier=expected[m],later=xs,provider=pre,decision='Preserve NJO canonical expectation; validate loaded scan.'))
  else:expected[m]=xs
 f=p/f'{pre}_EXPORT.json'
 if not f.exists():f=p/f'{pre}_EXPORTS.json'
 x=json.loads(f.read_text());rs=x.get('files',x.get('objects',[]))
 if isinstance(rs,dict):rs=[dict(v,path=k)for k,v in rs.items()]
 for row in rs:
  src=row.get('destination',row.get('path',''))
  if not any(src.endswith(s)for s in['.olean','.olean.private','.olean.server','.ir']):continue
  base=x.get('export',x.get('path',x.get('export_dir',x.get('directory',''))))
  rel=src[len(base)+1:] if base and src.startswith(base+'/')else src.split('/')[-1]
  seeds.append(dict(tag=pre,path=src,relative=rel,sha256=row['sha256'],bytes=row.get('bytes',row.get('size'))))
 if (p/f'{pre}_CONSUMER_PATHS.json').exists():paths=json.loads((p/f'{pre}_CONSUMER_PATHS.json').read_text())
 elif(p/f'{pre}_PATHS.json').exists():paths=json.loads((p/f'{pre}_PATHS.json').read_text())
 elif(p/f'{pre}_ENV_COMBINED.json').exists():paths=json.loads((p/f'{pre}_ENV_COMBINED.json').read_text())
 elif(p/f'{pre}_ENV.json').exists():paths=json.loads((p/f'{pre}_ENV.json').read_text())
 else:
  cs=[json.loads(f.read_text())['env']['LEAN_PATH']for f in sorted(p.glob(f'{pre}_L[0-9][0-9][0-9].json'))if 'LEAN_PATH'in json.loads(f.read_text()).get('env',{})];assert cs;paths=cs[-1]
 if isinstance(paths,dict):paths=paths.get('paths',paths.get('LEAN_PATH',paths.get('env',{}).get('LEAN_PATH')))
 if isinstance(paths,str):paths=paths.split(':')
 assert isinstance(paths,list),(pre,type(paths))
 extra+=paths
 for f in p.iterdir():
  if f.is_file()and any(k in f.name for k in['HANDOFF','CLOSED.json','ROW_PACKETS','COMBINED_IMPORT.lean','EXPORT','AUDIT_ROOTS','EXPECTED_IMPORTS','PHYSICAL','PLAN_STATUS','LEDGER.json.xz']):pins.append(dict(path=str(f.relative_to(E.parents[1])),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
roots=sorted(roots);n=30
(E/'NKC_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NKC_AUDIT_MODULES.json').write_text(json.dumps([['NKC_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
(E/'NKC_COMBINED_IMPORT.lean').write_text(''.join(f'import {pre}_COMBINED_IMPORT\n'for _,pre in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NJW_{name}.lean').read_text();t=s.replace('NJW_','NKC_');(E/f'NKC_{name}.lean').write_text(t);(E/f'NKC_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NJW_'+name,tofile='NKC_'+name)))
for p in E.glob('NKC_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'NKC_EXPECTED_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
(E/'NKC_SEED_INPUTS.json').write_text(json.dumps(seeds,indent=1)+'\n');(E/'NKC_INPUT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
paths=[C+'/'+pre+'_seed'for _,pre in specs]+extra
(E/'NKC_PATHS.json').write_text(json.dumps(list(dict.fromkeys(paths)),indent=1)+'\n')
for name in['run','batch','pin','setup','queue']:
 s=(P/f'NJW_{name}.py').read_text().replace('NJW_','NKC_').replace('codex-cx-ledger16-20261108','codex-cx-ledger17-20261108')
 if name=='run':s=s.replace("E.parent/'ledger15-20261108/NJO_CLOSURE_PINS.json.xz'","E.parent/'ledger16-20261108/NJW_CLOSURE_PINS.json.xz'")
 if name=='setup':s=s.replace("bytes=sum(r['bytes']for r in rows)","bytes=sum(Path(r['destination']).stat().st_size for r in rows)")
 (E/f'NKC_{name}.py').write_text(s)
print(json.dumps(dict(stage='prepare',roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
