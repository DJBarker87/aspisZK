"""Ledger23 owned client preparation; predecessor inputs are read only."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger22-20261110';Q=E.parent/'terminal6-20261110'
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLS_20261110'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
roots=set();expected={};conflicts=[];seeds=[];extras=[]
for folder,pre in [(P,'NLO'),(Q,'NLH')]:
 roots.update(J(folder/f'{pre}_AUDIT_ROOTS.json')['roots'])
 p=folder/f'{pre}_EXPECTED_IMPORTS.jsonl'
 if p.exists():raw=p.read_bytes()
 else:
  ref=J(Path(str(p)+'.ref.json'));raw=lzma.decompress((folder/ref['owned_input']).read_bytes());assert hashlib.sha256(raw).hexdigest()==ref['sha256']
 for l in raw.decode().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 x=J(folder/f'{pre}_EXPORT.json');base=x.get('export',x.get('path'))
 for r in x['files']:
  src=r.get('path',base+'/'+r.get('name',''));assert src.startswith(base+'/')
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=r['sha256'],bytes=r['bytes']))
 extras += [base]+(J(folder/'NLO_PATHS.json')if pre=='NLO'else x['lean_path'])
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NLS_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys([C+'/NLO_seed',C+'/NLH_seed']+extras))),('EXPECTED_CONFLICTS',conflicts)]:
 (E/f'NLS_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
# Import modules only, including NLH's module-only combined import. No private-name #check.
s='import NLO_COMBINED_IMPORT\nimport NLH_COMBINED_IMPORT\n#print axioms AspisR1.RPx_Deployed.deployed\n'
(E/'NLS_COMBINED_IMPORT.lean').write_text(s);(E/'NLO_COMBINED_IMPORT.lean').write_text(s)
for name in ['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NLO_{name}.lean').read_text().replace('NLO_','NLS_')
 (E/f'NLS_{name}.lean').write_text(s)
for name in ['run','batch','setup','queue','pin']:
 s=(P/f'NLO_{name}.py').read_text().replace('NLO_','NLS_').replace('codex-cx-ledger22-20261110','codex-cx-ledger23-20261110')
 s=s.replace("E.parent/'ledger21-20261110/NLG_CLOSURE_PINS.json.xz'","E.parent/'ledger22-20261110/NLO_CLOSURE_PINS.json.xz'")
 (E/f'NLS_{name}.py').write_text(s)
for p in E.glob('NLS_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NLS_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
assert not conflicts,conflicts
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
