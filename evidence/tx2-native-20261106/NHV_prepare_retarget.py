"""Import-only private replay of retained inactive decoder closure."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NHV_RETARGET_ANALYSIS.json').read_text());aliases=x['aliases'];mapping={m:'NHV_'+m.replace('.','_') for m in x['graph']};mapping.update(aliases)
seen=set();order=[]
def visit(m):
 if m in seen or m not in x['graph']:return
 seen.add(m)
 for n in x['graph'][m]:visit(n)
 order.append(m)
visit('NET_WideModel');records=[]
for m in order:
 before=x['sources'][m]['source'];body=[];imports=['NHT_COMBINED_IMPORT']
 for line in before.splitlines():
  if line.startswith('import '):
   for n in line[7:].split():
    n=mapping.get(n,n)
    if n not in imports:imports.append(n)
  else:body.append(line)
 after=''.join('import '+n+'\n' for n in imports)+'\n'+'\n'.join(body)+'\n'
 name=mapping[m];(E/(name+'.lean')).write_text(after)
 assert '\n'.join(z for z in before.splitlines() if not z.startswith('import '))=='\n'.join(body)
 records.append(dict(original_module=m,target=name,source=x['sources'][m]['path'],source_sha256=x['sources'][m]['sha256'],target_sha256=hashlib.sha256(after.encode()).hexdigest(),changes='import headers only; exact non-import body, quantifiers, hypotheses and proofs retained; generated limits unchanged'))
(E/'NHV_RETARGET_PROVENANCE.json').write_text(json.dumps(dict(aliases=aliases,records=records,order=[mapping[m] for m in order]),indent=2)+'\n')
print(json.dumps(dict(modules=len(order),first=[mapping[m] for m in order[:6]],last=mapping[order[-1]])))
