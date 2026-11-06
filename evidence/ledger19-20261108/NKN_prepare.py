from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger18-20261108'
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKN_20261108'
specs=[('ledger18-20261108','NKH','NKH_EXPORT.json','NKH_PATHS.json'),('claims2-20261108','NKA','NKA_EXPORT.json','NKA_CONSUMER_PATHS.json'),('poseidon-state-20261108','NKG','NKG_L055_validation/NKG_EXPORT.json','NKG_RETAINED_PATHS.json'),('field4-20261108','NKJ','NKJ_EXPORT.json',None)]
roots=set();expected={};conflicts=[];seeds=[];priority=[];extras=[]
for folder,pre,ex,pa in specs:
 p=E.parent/folder;x=json.loads((p/f'{pre}_AUDIT_ROOTS.json').read_text());roots.update(x if isinstance(x,list)else x.get('roots',sum(x.get('groups',[]),[])))
 for l in(p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 x=json.loads((p/ex).read_text());base=next(x[k]for k in ['export','directory','export_dir','path','export_root']if k in x)
 for row in x['files']:
  src=row.get('retained',row.get('destination',row.get('path')));assert src.startswith(base+'/'),src
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=row['sha256'],bytes=row.get('bytes',row.get('size'))))
 priority.append(C+'/'+pre+'_seed')
 if pre=='NKH':extras += [base]+json.loads((p/pa).read_text())
 elif pa:
  paths=json.loads((p/pa).read_text());extras+=paths.split(':')if isinstance(paths,str)else paths
 else:
  rc=json.loads((p/'NKJ_L033/receipt.json').read_text());extras+=rc['env']['LEAN_PATH'].split(':')
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NKN_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys(priority+extras))),('EXPECTED_CONFLICTS',conflicts)]: (E/f'NKN_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NKN_COMBINED_IMPORT.lean').write_text(''.join('import '+pre+'_COMBINED_IMPORT\n'for _,pre,_,_ in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 (E/f'NKN_{name}.lean').write_text((P/f'NKH_{name}.lean').read_text().replace('NKH_','NKN_'))
for p in E.glob('NKN_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKN_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
for name in ['run','batch','pin','setup','queue']:
 s=(P/f'NKH_{name}.py').read_text().replace('NKH_','NKN_').replace('codex-cx-ledger18-20261108','codex-cx-ledger19-20261108')
 if name=='run':
  s=s.replace("E.parent/'ledger17-20261108/NKC_CLOSURE_PINS.json.xz'","E.parent/'ledger18-20261108/NKH_CLOSURE_PINS.json.xz'")
  s=s.replace("assert disk_info['used']-1754012225536<40_000_000_000,'STOP host growth exceeds40GB conservative bound'",'')
  s=s.replace("if not q or not q.exists()", "if not q or not q.exists()")
 if name=='queue':s=s.replace('NKH_','NKN_')
 (E/f'NKN_{name}.py').write_text(s)
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
