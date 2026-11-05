from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;accepted={}
for p in E.glob('NIH_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
mods=[];roots=[];rejected=[]
for p in sorted(E.glob('NIH_*.lean')):
 if p.stem=='NIH_COMBINED_IMPORT' or not re.search(r'^theorem ',p.read_text(),re.M):continue
 r=accepted.get(p.stem);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if not r or r['source_hashes'].get('NIH_generated/'+p.name)!=sha:
  rejected.append(dict(module=p.stem,source_sha256=sha,reason='no successful current-source receipt; no object or theorem credit'));continue
 mods.append(dict(module=p.stem,attempt=r['attempt'],sha256=sha))
 for line in r['print_axioms']:
  assert 'sorryAx'not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1]not in roots:roots.append(m[1])
(E/'NIH_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n');(E/'NIH_REJECTED_DRAFTS.json').write_text(json.dumps(rejected,indent=2)+'\n')
(E/'NIH_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+16] for i in range(0,len(roots),16)]),indent=2)+'\n')
imports=['NGK_COMBINED_IMPORT','NHU_COMBINED_IMPORT',*[r['module'] for r in mods]]
body='\n'.join('import '+name for name in imports)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n'+'\n'.join('#print axioms '+root for root in roots)+'\n';(E/'NIH_COMBINED_IMPORT.lean').write_text(body)
rows={r['module']:r for r in map(json.loads,(E/'NIH_EXPECTED_IMPORTS_BASE.jsonl').read_text().splitlines())}
for module in [*[r['module'] for r in mods],'NIH_COMBINED_IMPORT']:
 src=(E/(module+'.lean')).read_text();rows[module]=dict(module=module,imports=['Init',*re.findall(r'^import ([\w.]+)',src,re.M)])
(E/'NIH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[k])+'\n' for k in sorted(rows)))
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+15)//16,rejected=[x['module'] for x in rejected])))
