"""Associate historical S certificates with canonical theorem names and receipts."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger7-20261104';R=E.parents[1]
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
baseline=json.loads(lzma.decompress((P/'NFX_LEDGER.json.xz').read_bytes()));prov=J(E/'NFY_PROVENANCE.json');delta=J(E/'NFY_LEDGER_DELTA.json');audit=J(E/'NFY_AUDIT.json');ren=prov['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
latest={}
for p in sorted(E.glob('NFY_L*/receipt.json')):
 r=J(p)
 if r.get('kind')=='lean' and r['exit_status']==0:latest[r['module']]=(p,r)
mods={r['module'] for r in map(json.loads,(E/'NFY_LOADED_scan.jsonl').read_text().splitlines())};audited={r['root'] for r in audit['results']}
records=[];allnames=set();gaps=[]
root_owner={n:m for m,ns in J(E/'NFY_TOP_ROOTS.json')['modules'].items() for n in ns}
reviewed=[dict(row=r['row']) for r in baseline['rows'] if r['composed_status']=='QUALIFIED'];assert len(reviewed)==89
for promotion in reviewed:
 rid=promotion['row'];row=next(r for r in baseline['rows'] if r['row']==rid)
 cert=baseline.get('NFK_certificates',{}).get(rid,baseline.get('NEZ_certificates',{}).get(rid))
 if cert is None:cert=row
 refs=[]
 def walk(v):
  if isinstance(v,dict):
   if isinstance(v.get('name'),str) and isinstance(v.get('source'),dict) and 'statement' in v:
    old=v['name'];new=pat.sub(lambda m:ren[m.group()],old);source=v['source']['path'];module=Path(source).stem
    if module not in prov['module_owner']:
     matches=[n for n in old.split('.') if n in prov['module_owner']]
     if matches:module=matches[0]
     elif module.endswith('.lean'):
      bits=old.split('.');module=bits[1] if bits[0]=='AspisR1' else bits[0]
    target=prov['module_owner'].get(module,module)
    if target not in mods and new in root_owner:target=root_owner[new]
    if target not in mods:gaps.append(dict(row=rid,legacy_name=old,canonical_name=new,unloaded_module=target,source=source,reason='Selected historical certificate names a Lean declaration whose module is outside the combined canonical import. No coherence credit for that occurrence until its exact statement is retargeted and replayed.'))
    rec=dict(legacy_name=old,canonical_name=new,legacy_source=v['source'],legacy_receipt=v.get('receipt'),canonical_module=target,statement_before=v['statement'],statement_after_qualified_names=pat.sub(lambda m:ren[m.group()],v['statement']),raw_top_audited=new in audited)
    if target in latest:
     path,r=latest[target];rec.update(canonical_source=dict(path=str((E/(target+'.lean')).relative_to(R)),sha256=H((E/(target+'.lean')).read_bytes())),canonical_receipt=dict(path=str(path.relative_to(R)),sha256=H(path.read_bytes())))
    elif target in mods:rec['canonical_support']='Reused admitted NFX object; exact object identity in NFY_CLOSURE_PINS.json.xz and import cache manifests; no duplicated proof.'
    else:rec['canonical_support']='OPEN: module not loaded; exact canonical retarget and replay required.'
    refs.append(rec);allnames.add(new)
   for x in v.values():walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 walk(cert)
 unique={json.dumps(r,sort_keys=True):r for r in refs}
 records.append(dict(row=rid,function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],historical_certificate_sha256=H(json.dumps(cert,sort_keys=True).encode()),historical_certificate_container='evidence/ledger7-20261104/NFX_LEDGER.json.xz',canonical_theorem_associations=list(unique.values()),selected_claims_retained=row['selected_claims'],domain_and_trust_fields='Historical certificate unchanged; exact copied before/after theorem bodies and helper transports are in NFY_PROVENANCE.json/NFY_STATEMENT_TRANSPORT.json.',claim='Candidate theorem associations only; row admission is governed exclusively by NFY_LEDGER_DELTA.json and its missing-reference/selected-callee checks; no new native pass or trust removal'))
(E/'NFY_CERTIFICATES.json').write_text(json.dumps(dict(rows=records,distinct_theorem_associations=len(allnames),raw_top_audited=sum(n in audited for n in allnames),unrequested_unreached_helpers=sorted(allnames-audited)),indent=1)+'\n')
gaps=list({(g['row'],g['canonical_name'],g['unloaded_module']):g for g in gaps}.values())
(E/'NFY_CERTIFICATE_GAPS.json').write_text(json.dumps(gaps,indent=1)+'\n')
print(json.dumps(dict(rows=len(records),names=len(allnames),top_audited=sum(n in audited for n in allnames),gaps=len(gaps),gap_rows=sorted({g['row'] for g in gaps}))))
