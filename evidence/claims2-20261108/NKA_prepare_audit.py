from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;accepted={}
for p in sorted(E.glob('NKA_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
sources={p.stem:p for p in E.glob('NKA_*.lean') if p.stem not in ['NKA_Driver','NKA_ProofDriver','NKA_COMBINED_IMPORT','NKA_Statements']}
mods=[];roots=['AspisR1.RPx_Deployed.deployed']
for name,p in sorted(sources.items()):
 r=accepted.get(name);h=hashlib.sha256(p.read_bytes()).hexdigest();assert r and h in r['source_hashes'].values(),('missing current successful compile',name)
 mods.append(dict(module=name,attempt=r['attempt'],sha256=h,source=p.name))
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1] not in roots:roots.append(m[1])
(E/'NKA_MODULES.json').write_text(json.dumps(mods,indent=2))
(E/'NKA_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+24] for i in range(0,len(roots),24)]),indent=2))
(E/'NKA_COMBINED_IMPORT.lean').write_text('\n'.join('import '+n for n in ['NJW_COMBINED_IMPORT','NJT_COMBINED_IMPORT',*[m['module'] for m in mods]])+'\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
rows={};variants=[]
for path in [E.parent/'ledger16-20261108/NJW_EXPECTED_IMPORTS.jsonl',E.parent/'claims-queryscan-20261108/NJT_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line);n=x['module']
  if n in rows and rows[n]['imports']!=x['imports']:variants.append(dict(module=n,old=rows[n],new=x))
  rows[n]=x
for n,p in [('NKA_COMBINED_IMPORT',E/'NKA_COMBINED_IMPORT.lean'),*sources.items()]:
 imports=re.findall(r'^import ([\w.]+)',p.read_text(),re.M);rows[n]=dict(module=n,imports=list(dict.fromkeys(['Init',*imports])))
(E/'NKA_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)))
(E/'NKA_IMPORT_VARIANTS.json').write_text(json.dumps(variants,indent=2))
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+23)//24,variants=len(variants))))
