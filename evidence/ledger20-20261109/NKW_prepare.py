from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger19-20261108';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKW_20261109'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
specs=[('ledger19-20261108','NKN','NKN_EXPORT.json'),('circle-points-20261108','NKM',None),('terminal4-20261108','NKI','NKI_EXPORT.json'),('batch-merkle3-20261108','NKL','NKL_EXPORT.json'),('tx2-adapters2-20261108','NKP','NKP_EXPORT_FINAL.json')]
roots=set();expected={};conflicts=[];seeds=[];priority=[];extras=[]
for folder,pre,ex in specs:
 p=E.parent/folder;x=J(p/f'{pre}_AUDIT_ROOTS.json');roots.update(x if isinstance(x,list)else x.get('roots',sum(x.get('groups',[]),[])))
 for l in(p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 if ex:
  x=J(p/ex);base=next(x[k]for k in ['export','directory','export_dir','path','export_root','destination']if k in x)
  for row in x['files']:
   src=row.get('retained',row.get('destination',row.get('path')));assert src.startswith(base+'/'),src
   seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=row['sha256'],bytes=row.get('bytes',row.get('size'))))
 else:
  x=J(p/'NKM_CLOSURE_PINS.json.xz');base='/home/dombarker/project-offloads/codex-cx-circle-points-20261108/NKM_objects'
  for row in x['files'].values():
   if row['path'].startswith(base+'/'):seeds.append(dict(tag=pre,path=row['path'],relative=row['path'][len(base)+1:],sha256=row['sha256'],bytes=row['bytes']))
 priority.append(C+'/'+pre+'_seed')
 if pre=='NKN':extras += [base]+J(p/'NKN_PATHS.json')
 elif pre=='NKM':extras+=x['selected_order']
 elif pre=='NKI':extras+=J(p/'NKI_L090/receipt.json')['env']['LEAN_PATH'].split(':')
 else:extras+=J(p/(pre+'_ENV.json'))['LEAN_PATH'].split(':')
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NKW_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys(priority+extras))),('EXPECTED_CONFLICTS',conflicts)]: (E/f'NKW_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NKW_COMBINED_IMPORT.lean').write_text(''.join('import '+pre+'_COMBINED_IMPORT\n'for _,pre,_ in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 (E/f'NKW_{name}.lean').write_text((P/f'NKN_{name}.lean').read_text().replace('NKN_','NKW_'))
for p in E.glob('NKW_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKW_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
for name in ['run','batch','setup','queue']:
 s=(P/f'NKN_{name}.py').read_text().replace('NKN_','NKW_').replace('codex-cx-ledger19-20261108','codex-cx-ledger20-20261109').replace('NKW_20261108','NKW_20261109')
 if name=='run':s=s.replace("resubmission_after_host_repair=(a=='NKW_L026'),resubmits_attempt='NKW_L025' if a=='NKW_L026' else None,",'')
 (E/f'NKW_{name}.py').write_text(s)
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
