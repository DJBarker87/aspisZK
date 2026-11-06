from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;accepted={}
for p in sorted(E.glob('NJM_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
mods=[];roots=['AspisR1.RPx_Deployed.deployed'];excluded=[]
for p in sorted(E.glob('NJM_*.lean')):
 if p.stem.startswith('NJM_Inspect') or p.stem in ['NJM_Driver','NJM_ProofDriver','NJM_COMBINED_IMPORT','NJM_Statements']:continue
 r=accepted.get(p.stem);h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not r or r['source_hashes'].get('NJM_generated/'+p.name)!=h:
  excluded.append(dict(module=p.stem,sha256=h,reason='No successful current-source receipt'));continue
 mods.append(dict(module=p.stem,attempt=r['attempt'],sha256=h))
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1] not in roots:roots.append(m[1])
assert {'NJM_InvocationRoots','NJM_RoundAllArgs','NJM_RoundsClosed','NJM_CircleRoot','NJM_CircleInvalid'}.issubset({x['module'] for x in mods})
(E/'NJM_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
(E/'NJM_EXCLUDED_DRAFTS.json').write_text(json.dumps(excluded,indent=2)+'\n')
(E/'NJM_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+24] for i in range(0,len(roots),24)]),indent=2)+'\n')
(E/'NJM_COMBINED_IMPORT.lean').write_text('\n'.join('import '+n for n in ['NJK_COMBINED_IMPORT','NJG_COMBINED_IMPORT',*[m['module'] for m in mods]])+'\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
rows={};variants=[]
for path in [E.parent/'ledger14-20261108/NJK_EXPECTED_IMPORTS.jsonl',E.parent/'verify-observed6-20261107/NJG_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line);n=x['module']
  if n in rows and rows[n]['imports']!=x['imports']:variants.append(dict(module=n,old=rows[n],new=x))
  rows[n]=x
for n in ['NJM_COMBINED_IMPORT',*[m['module'] for m in mods]]:
 text=(E/(n+'.lean')).read_text();imports=re.findall(r'^import ([\w.]+)',text,re.M)
 rows[n]=dict(module=n,imports=list(dict.fromkeys(["Init",*imports])))
(E/'NJM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)))
(E/'NJM_IMPORT_VARIANTS.json').write_text(json.dumps(variants,indent=2)+'\n')
(E/'NJM_AUDIT_MODULES.json').write_text(json.dumps([m['module'] for m in mods],indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+23)//24,expected_import_variants=len(variants))))
