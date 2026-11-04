"""Enumerate every theorem record, independently of loaded-module filters."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-retarget-20261104';J=lambda p:json.loads(p.read_text())
b=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));prov=J(E/'NGE_PROVENANCE.json');ren=prov['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])');baseline={r['row']:r for r in J(P/'NFY_CERTIFICATES.json')['rows']};out=[]
for row in b['rows']:
 if row['row'] not in baseline:continue
 rid=row['row'];cert=b.get('NFK_certificates',{}).get(rid,b.get('NEZ_certificates',{}).get(rid,row));records=[]
 def walk(v):
  if isinstance(v,dict):
   if isinstance(v.get('name'),str) and isinstance(v.get('source'),dict) and 'statement' in v:
    records.append(v)
   for q in v.values():walk(q)
  elif isinstance(v,list):
   for q in v:walk(q)
 walk(cert)
 assert {r['name'] for r in records}=={r['legacy_name'] for r in baseline[rid]['canonical_theorem_associations']},rid
 refs=[]
 for r in baseline[rid]['canonical_theorem_associations']:
  module=prov['module_owner'].get(r['canonical_module'],r['canonical_module']);new=pat.sub(lambda m:ren[m.group()],r['legacy_name'])
  refs.append(dict(legacy_name=r['legacy_name'],canonical_name=new,canonical_module=module,statement_before=r['statement_before'],statement_after=pat.sub(lambda m:ren[m.group()],r['statement_before']),source=r['legacy_source']))
 out.append(dict(row=rid,function=row['function'],recursive_record_count=len(records),theorems=refs))
(E/'NGE_CERTIFICATES.json').write_text(json.dumps(dict(rows=out,record_count=sum(r['recursive_record_count'] for r in out),inventory_method='Recursive traversal of every selected certificate; no loaded-graph or name filter'),indent=1)+'\n')
print(json.dumps(dict(rows=len(out),records=sum(r['recursive_record_count'] for r in out),distinct_names=len({r['canonical_name'] for x in out for r in x['theorems']}))))
