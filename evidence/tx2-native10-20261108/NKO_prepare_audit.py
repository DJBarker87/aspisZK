"""Select current focused-green sources; create one combined import/audit plan."""
from pathlib import Path
import hashlib,json,re
from NKO_read import read_text
E=Path(__file__).resolve().parent
latest={}
for line in (E/'NKO_ATTEMPTS.jsonl').read_text().splitlines():
 entry=json.loads(line)
 if entry['kind']!='lean':continue
 p=E/entry['full_receipt'];r=json.loads(p.read_text())
 latest[r['module']]=(p.parent.name,r)
latest={m:row for m,row in latest.items() if row[1]['exit_status']==0}
modules=[];roots=[];source_rows=[]
for m,(a,r) in sorted(latest.items()):
 if m in ['NKO_Driver','NKO_ProofDriver','NKO_COMBINED_IMPORT']:continue
 p=E/(m+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 expected=r['source_hashes']['NKO_generated/'+m+'.lean']
 assert sha==expected,('changed source after focused proof',m)
 modules.append(m);source_rows.append(dict(module=m,attempt=a,sha256=sha))
 for line in r['print_axioms']:
  match=re.search("'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if match and match[1] not in roots:roots.append(match[1])
for x in ['AspisR1.NJU_GeneralFinishRoot.finish','AspisR1.NJU_GeneralFinishRoot.ported','NJU_FinishAtCurrent.source_view','AspisR1.RPx_Deployed.deployed']:
 if x not in roots:roots.append(x)
(E/'NKO_MODULES.json').write_text(json.dumps(modules,indent=2)+'\n')
(E/'NKO_SELECTED_SOURCES.json').write_text(json.dumps(source_rows,indent=2)+'\n')
imports=['NKH_COMBINED_IMPORT','NKE_COMBINED_IMPORT']+modules
(E/'NKO_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+'\nset_option pp.proofs false\n#print AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
rows={json.loads(l)['module']:json.loads(l) for l in read_text(E/'NKO_BASE_EXPECTED_IMPORTS.jsonl').splitlines()}
for m in modules+['NKO_COMBINED_IMPORT']:
 imp=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)
 rows[m]={'module':m,'imports':list(dict.fromkeys(imp))}
(E/'NKO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[m],separators=(',',':'))+'\n' for m in sorted(rows)))
groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/'NKO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
p=E/'NKO_ProofDriver.lean';s=p.read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NKO_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:];p.write_text(s)
print(json.dumps(dict(selected_modules=len(modules),raw_roots=len(roots),groups=len(groups),expected_modules=len(rows))))
