"""Select current focused-green sources; create one combined import/audit plan."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
latest={}
for p in sorted(E.glob('NKE_L*/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=(p.parent.name,r)
modules=[];roots=[];source_rows=[]
for m,(a,r) in sorted(latest.items()):
 if m in ['NKE_Driver','NKE_ProofDriver','NKE_COMBINED_IMPORT']:continue
 p=E/(m+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 expected=r['source_hashes']['NKE_generated/'+m+'.lean']
 assert sha==expected,('changed source after focused proof',m)
 modules.append(m);source_rows.append(dict(module=m,attempt=a,sha256=sha))
 for line in r['print_axioms']:
  match=re.search("'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if match and match[1] not in roots:roots.append(match[1])
for x in ['AspisR1.NJU_GeneralFinishRoot.finish','AspisR1.NJU_GeneralFinishRoot.ported','NJU_FinishAtCurrent.source_view','AspisR1.RPx_Deployed.deployed']:
 if x not in roots:roots.append(x)
(E/'NKE_MODULES.json').write_text(json.dumps(modules,indent=2)+'\n')
(E/'NKE_SELECTED_SOURCES.json').write_text(json.dumps(source_rows,indent=2)+'\n')
imports=['NKC_COMBINED_IMPORT','NJU_COMBINED_IMPORT']+modules
(E/'NKE_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+'\nset_option pp.proofs false\n#print AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
rows={json.loads(l)['module']:json.loads(l) for l in (E/'NKE_BASE_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for m in modules+['NKE_COMBINED_IMPORT']:
 imp=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)
 rows[m]={'module':m,'imports':list(dict.fromkeys(imp))}
(E/'NKE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[m],separators=(',',':'))+'\n' for m in sorted(rows)))
groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/'NKE_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
p=E/'NKE_ProofDriver.lean';s=p.read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NKE_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:];p.write_text(s)
print(json.dumps(dict(selected_modules=len(modules),raw_roots=len(roots),groups=len(groups),expected_modules=len(rows))))
