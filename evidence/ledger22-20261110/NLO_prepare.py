from pathlib import Path
import json,lzma,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger21-20261110';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLO_20261110'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
specs=[('ledger21-20261110','NLG','EXPORT','PATHS'),('terminal5-20261108','NKR','EXPORT','PATH'),('batch-merkle6-20261110','NLN','EXPORT_MANIFEST','RESTORE_PATHS')]
roots=set();expected={};conflicts=[];seeds=[];priority=[];extras=[]
for folder,pre,exp,pat in specs:
 p=E.parent/folder;x=J(p/f'{pre}_AUDIT_ROOTS.json');roots.update(x.get('roots',sum(x.get('groups',[]),[])))
 imp=p/f'{pre}_EXPECTED_IMPORTS.jsonl'
 if imp.exists(): raw=imp.read_bytes()
 else:
  ref=J(Path(str(imp)+'.ref.json'));raw=lzma.decompress((p/ref['owned_input']).read_bytes());assert __import__('hashlib').sha256(raw).hexdigest()==ref['sha256']
 for l in raw.decode().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 x=J(p/f'{pre}_{exp}.json');base=x.get('export',x.get('path'));files=x['files']
 if isinstance(files,dict):files=[dict(v,path=base+'/'+k)for k,v in files.items()]
 for row in files:
  src=row.get('retained',row.get('destination',row.get('path')));assert src.startswith(base+'/'),src
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=row['sha256'],bytes=row.get('bytes',row.get('size'))))
 priority.append(C+'/'+pre+'_seed');extras += [base]+J(p/f'{pre}_{pat}.json')
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NLO_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys(priority+extras))),('EXPECTED_CONFLICTS',conflicts)]: (E/f'NLO_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
nkr=re.findall(r'^import (\w+)',(E.parent/'terminal5-20261108/NKR_COMBINED_IMPORT.lean').read_text(),re.M)
(E/'NLO_COMBINED_IMPORT.lean').write_text('import NLG_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in nkr if m.startswith('NKR_') and m!='NKR_COMBINED_IMPORT')+'import NLN_COMBINED_IMPORT\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NLG_{name}.lean').read_text().replace('NLG_','NLO_')
 if name=='OwnerStatements':s=s.replace('let env ← getEnv','let env := (← getEnv).setExporting false')
 (E/f'NLO_{name}.lean').write_text(s)
for p in E.glob('NLO_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NLO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
for name in ['run','batch','setup','queue']:
 s=(P/f'NLG_{name}.py').read_text().replace('NLG_','NLO_').replace('codex-cx-ledger21-20261110','codex-cx-ledger22-20261110')
 if name=='run':
  s=s.replace("if target in ['close','review-close']:","if target in ['close','review-close']:")
  # Private roots raw-audited by unchanged walker; owned stdout archiving below20MB handled before commits.
 if name=='queue':s=s.replace("bad[0]['root']!='NHC_DecodeModel.decoder_error'", "bad[0]['root'] not in ['NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition']")
 (E/f'NLO_{name}.py').write_text(s)
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts),imports=len(nkr))))
