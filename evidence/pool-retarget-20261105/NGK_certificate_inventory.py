"""Inventory all selected theorem records before any loaded-module lookup."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent
x=json.loads((E/'NGK_PROVENANCE.json').read_text());rename=x['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
records=[]
# All predecessor raw audit roots, including ones omitted by the final aggregate.
for d,n in [('pool-retdata-20261104','NFO'),('pool-retdata2-20261104','NFR'),('pool-retdata3-20261104','NFV')]:
 p=P/d/(n+'_AUDIT.json');audit=json.loads(p.read_text());roots=audit['roots']
 if isinstance(roots,dict):roots=list(roots.values())
 for r in roots:
  name=r if isinstance(r,str) else r.get('root',r.get('name'))
  if not name:continue
  records.append(dict(certificate=str(p.relative_to(E.parents[1])),certificate_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),legacy_name=name,canonical_name=pat.sub(lambda m:rename[m.group()],name),record=r))
# The COMPLETE selected sources, including all auxiliary/domain/frame theorems,
# not just a root/name filter. Exact full before/after statements remain in
# provenance bodies. Compiler-owned enumeration is added after successful replay.
for r in x['files']:
 for m in re.finditer(r'(?m)^(?:private )?theorem\s+([^\s({:]+)',r['before_body']):
  start=m.start();end=r['before_body'].find('\n#print axioms',start)
  if end<0:end=len(r['before_body'])
  text=r['before_body'][start:end]
  records.append(dict(certificate=r['source_path'],source_sha256=r['source_sha256'],source_module=r['source_module'],local_name=m[1],statement_and_proof_before=text,statement_and_proof_after=pat.sub(lambda m:rename[m.group()],text)))
(E/'NGK_CERTIFICATES.json').write_text(json.dumps(records,indent=1)+'\n');print(len(records),'theorem record occurrences')
