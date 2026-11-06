from pathlib import Path
import json,lzma,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger20-20261109';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLG_20261110'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
specs=[('ledger20-20261109','NKW'),('tx2-resume2-20261109','NKU'),('row-bridges-20261109','NKY')]
roots=set();expected={};conflicts=[];seeds=[];priority=[];extras=[]
for folder,pre in specs:
 p=E.parent/folder;x=J(p/f'{pre}_AUDIT_ROOTS.json');roots.update(x.get('roots',sum(x.get('groups',[]),[])))
 for l in(p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 x=J(p/f'{pre}_EXPORT.json');base=next(x[k]for k in ['export','path']if k in x)
 for row in x['files']:
  src=row.get('retained',row.get('destination',row.get('path')));assert src.startswith(base+'/'),src
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=row['sha256'],bytes=row.get('bytes',row.get('size'))))
 priority.append(C+'/'+pre+'_seed');extras += [base]+J(p/f'{pre}_PATHS.json')
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NLG_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys(priority+extras))),('EXPECTED_CONFLICTS',conflicts)]: (E/f'NLG_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NLG_COMBINED_IMPORT.lean').write_text(''.join('import '+pre+'_COMBINED_IMPORT\n'for _,pre in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 (E/f'NLG_{name}.lean').write_text((P/f'NKW_{name}.lean').read_text().replace('NKW_','NLG_'))
for p in E.glob('NLG_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NLG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
for name in ['run','batch','setup','queue']:
 s=(P/f'NKW_{name}.py').read_text().replace('NKW_','NLG_').replace('codex-cx-ledger20-20261109','codex-cx-ledger21-20261110').replace('NLG_20261109','NLG_20261110')
 (E/f'NLG_{name}.py').write_text(s)
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
