"""Resolve source-cohort type snapshots through retained accepted receipts."""
import pathlib,json,hashlib,lzma
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence');base=pathlib.Path('evidence/pv-lib-20261107');groups=json.loads((E/'SOURCE_DRIVERS.json').read_text());receipts=[]
for p in base.rglob('receipt-*.json'):
 if 'v1-coherence' in str(p):continue
 try:r=json.loads(p.read_text())
 except ValueError:continue
 if r.get('accepted'):receipts.append((p,r))
out=[];missing=[]
for g in groups:
 source=pathlib.Path('lean',g['driver']+'.lean').read_bytes();h=hashlib.sha256(source).hexdigest()
 candidates=[(p,r) for p,r in receipts if r.get('target')==g['driver'] and r.get('source_sha256')==h]
 candidates.sort(key=lambda pr:(not pr[1].get('runtime_audit',False),-pr[1].get('attempt',0)))
 found=None
 for p,r in candidates:
  a=r['attempt'];res=p.parent/f'resolution-{a}.json.xz'
  if res.exists():
   z=json.loads(lzma.decompress(res.read_bytes()));z=z.get('modules',z)
   if all(m in z for m in g['modules']):found=(p,r,res,z);break
 if not found:
  fallback={'PV_LIB_SPEC_RawAuditSession19':56207,'PV_LIB_SPEC_RawAuditBase':49711,'PV_LIB_SPEC_RawAuditStx':49712,'PV_LIB_SPEC_RawAuditSession2':49723}
  if g['driver'] in fallback:
   a=fallback[g['driver']];out.append(dict(**g,attempt=a,host_resolution=f'/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/evidence/resolution-{a}.json.xz'));continue
  if g['driver']=='PV_LIB_A_RawAudit12':
   res=base/'lane-A/session12/resolution-47497.json.xz';z=json.loads(lzma.decompress(res.read_bytes()));z=z.get('modules',z)
   assert all(m in z for m in g['modules'])
   out.append(dict(**g,attempt=47497,resolution=z,resolution_file=str(res),baseline_qualification='Source cohort type snapshot only; historical audit47497 was nonzero and is not credited as passing.'));continue
  missing.append(g['driver']);continue
 p,r,res,z=found
 out.append(dict(**g,source_sha256=h,receipt=str(p),attempt=r['attempt'],resolution_file=str(res),resolution=z))
inv=json.loads((E/'INVENTORY.json').read_text());covered={r for g in out for r in g['roots']};extra=set(inv['root_provenance'])-covered
rank={'PV_LIB_RawAudit2':0,'PV_LIB_RawAudit':1,'PV_LIB_SLICE_RawAudit4':2,'PV_LIB_A_RawAudit16':3}
for root in sorted(extra):
 ns=root.rsplit('.',1)[0]
 candidates=[g for g in out if ns in g.get('resolution',{}) or any(r.rsplit('.',1)[0]==ns for r in g['roots'])]
 assert candidates,('manifest root without source cohort',root)
 g=min(candidates,key=lambda g:rank.get(g['driver'],10));g['roots'].append(root);g.setdefault('manifest_extra_roots',[]).append(root)
 if ns in g.get('resolution',{}) and ns not in g['modules']:g['modules'].append(ns)
assert set(inv['root_provenance'])<={r for g in out for r in g['roots']}
(E/'SNAPSHOT_PLAN.json.xz').write_bytes(lzma.compress(json.dumps(out).encode()))
(E/'SNAPSHOT_MISSING.json').write_text(json.dumps(missing,indent=2)+'\n');print('resolved groups',len(out),'missing',len(missing),missing)
