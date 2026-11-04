"""Locate active S packet module paths to the measured legacy defects."""
from pathlib import Path
import json,lzma,re,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
rows=[json.loads(l) for l in (E/'NFX_audit/inventory-s/inventory-s.log').read_text().splitlines() if l.startswith('{')]
g={r['module']:r['imports'] for r in rows};bad={r['module'] for r in rows if r['dangling']};assert len(bad)==15 and sum(len(r['dangling']) for r in rows)==650
base=json.loads(lzma.decompress((R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read_bytes()))
spec=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices'];shared=set(spec['S']['functions'])&set(spec['Q']['functions'])
def find_path(start):
 todo=collections.deque([(start,[start])]);seen=set()
 while todo:
  n,p=todo.popleft()
  if n in seen:continue
  seen.add(n)
  if n in bad:return p
  todo.extend((d,p+[d]) for d in g.get(n,[]))
 return None
# This primitive theorem is an active S packet root absent from NFJ's
# 88-root aggregate. Follow its exact committed import too.
source=R/'evidence/slice-s-compose2-20261029/NEE_M31SerializerDomain.lean'
g['NEE_M31SerializerDomain']=re.findall(r'^import ([\w.]+)',source.read_text(),re.M)
paths={m:find_path(m) for m in g}
def strings(v):
 if isinstance(v,str):yield v
 elif isinstance(v,dict):
  for k,x in v.items():yield k;yield from strings(x)
 elif isinstance(v,list):
  for x in v:yield from strings(x)
result=[]
for row in base['rows']:
 if row['function'] not in spec['S']['functions'] or row['function'] in shared:continue
 cert=base.get('NFK_certificates',{}).get(row['row'],base.get('NEZ_certificates',{}).get(row['row']))
 if cert is None:cert=row
 modules=set()
 # Match theorem names and committed Lean source/receipt module identifiers.
 for s in strings(cert):
  for token in re.findall(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',s):
   bits=token.split('.')
   for i in range(len(bits)):
    m='.'.join(bits[:i+1])
    if m in g:modules.add(m)
    if bits[i] in g:modules.add(bits[i])
 offending={m:paths[m] for m in sorted(modules) if paths[m]}
 result.append(dict(row=row['row'],function=row['function'],certificate_found=cert is not row,referenced_modules=sorted(modules),legacy_paths=offending,status='QUALIFIED' if offending else 'NEEDS_EXACT_PACKET_FOREST_REVIEW',reason='Active selected certificate imports the measured legacy forest (650 dangling references in 15 modules); faithful S+headline import also fails duplicate PrepQM ownership. Source-validator CLOSED retained historically; no headline coherence credit.'))
(E/'NFX_S_PACKET_PATHS.json').write_text(json.dumps(result,indent=1)+'\n')
denials=[dict(row=r['row'],reason=r['reason'],legacy_paths=r['legacy_paths']) for r in result if r['legacy_paths']]
(E/'NFX_COHERENCE_DENIALS.json').write_text(json.dumps(denials,indent=1)+'\n')
print(json.dumps(dict(S_rows=len(result),qualified=len(denials),unresolved=[r['row'] for r in result if not r['legacy_paths']],bad_modules=sorted(bad))))
