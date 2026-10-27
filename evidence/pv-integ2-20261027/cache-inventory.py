from pathlib import Path
import json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-integ2-20261027');B=D.parent;J=B/'aspis-joint-20261019'
plan=json.loads((D/'formal-plan.json').read_text());env=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
# Read-only fallbacks owned by the integrated jobs; no blanket cache overlay.
extras=[]
for name in ['codex-pv-cb3-20261026','codex-pv-cbmid-20261027','codex-pv-op134-20261027','codex-pv-cblib-20261027','codex-pv-join-20261026','codex-pv-l2b-20261027','codex-pv-op223-20261027','codex-pv-cb-20261026']:
 for suffix in ['objects','lean-objects','']:
  r=B/name/suffix
  if r.is_dir():extras.append(r)
rows=[]
for n,v in plan['closure'].items():
 if not n.startswith(('R1Z.PV_','PV_L2B_')):continue
 rel=Path(n.replace('.','/')+'.olean'); found=[]
 for r in roots+extras:
  p=r/rel
  if p.is_file() and str(p) not in [x['object'] for x in found]:
   sources=[J/'sources'/rel.with_suffix('.lean'),r.parent/'sources'/rel.with_suffix('.lean'),r.parent/'lean-sources'/rel.with_suffix('.lean'),r/rel.with_suffix('.lean'),r.parent/rel.with_suffix('.lean')]
   checks=[dict(path=str(s),sha256=hashlib.sha256(s.read_bytes()).hexdigest()) for s in sources if s.is_file()]
   found.append(dict(object=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),sources=checks))
 rows.append(dict(module=n,expected=v,available=found))
(D/'cache-inventory.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PV closure',len(rows),'missing',sum(not r['available'] for r in rows),'source mismatch',sum(bool(r['available']) and not any(s['sha256']==r['expected']['sha256'] for f in r['available'] for s in f['sources']) for r in rows))
print('missing modules:',[r['module'] for r in rows if not r['available']])
