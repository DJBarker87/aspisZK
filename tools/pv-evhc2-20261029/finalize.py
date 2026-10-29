"""Validate reconciled closure and write READY, without launching any compiler."""
from pathlib import Path
import json,hashlib,time
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.load(open(B/'plan.json'));ndr=json.load(open(B/'NDR_FINAL_COHORT_PINS.json'))
receipts=[json.load(open(p)) for p in sorted(B.glob('lean-*/receipt.json'))]
assert {r['module'] for r in receipts}==set(plan['rebuild'])
assert all(r['exit_status']==0 and r['swaps']=='0' and int(r['peak_rss_kib'])<=7*1024*1024 for r in receipts)
assert not (B/'STOP.json').exists()
rows={v['module']:dict(module=v['module'],path=v['object_path'],sha256=v['object_sha256'],cohort='NDR') for v in ndr['entries']}
output=json.load(open(B/'NDR_FINAL_OUTPUT_PINS.json'))['objects/NDR_CombinedAudit.olean']['sha256']
rows['NDR_CombinedAudit']=dict(module='NDR_CombinedAudit',path=str(B.parent/'codex-cx-reconcile-cache-20261028/objects/NDR_CombinedAudit.olean'),sha256=output,cohort='NDR final output')
for m in plan['rebuild']+plan['reuse']:
 p=B/'objects'/(m.replace('.','/')+'.olean');rows[m]=dict(module=m,path=str(p),sha256=sha(p),cohort='reconciled rebuild' if m in plan['rebuild'] else 'fingerprint-checked reuse',companions=[])
 for q in [Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]:
  if q.exists():rows[m]['companions'].append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
# Every dependency selected by the READY path must be the recorded authoritative object.
roots=[B/'objects',B.parent/'codex-cx-reconcile-cache-20261028/objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
for m,r in rows.items():
 p=next(root/(m.replace('.','/')+'.olean') for root in roots if (root/(m.replace('.','/')+'.olean')).exists())
 assert sha(p)==r['sha256'],('effective object mismatch',m)
manifest=dict(authoritative_cohort='NDR',authoritative_manifest_sha256=plan['ndr_manifest_sha256'],entries=list(rows.values()),rebuild=plan['rebuild'],reuse=plan['reuse'])
(B/'COHORT-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary=dict(modules_rebuilt=len(receipts),modules_reused=len(plan['reuse']),compile_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),attempts=[r['attempt'] for r in receipts],proof_attempts=0,mechanical_attempts=len(receipts),consumer_compile_run=False,consumer_axioms='not run: pending lead authorization',print_axioms={r['module']:r['print_axioms'] for r in receipts})
(B/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
ready=dict(status='READY FOR LEAD REVIEW; NO AGGREGATION AUTHORIZED',LEAN_PATH=':'.join(map(str,roots)),cohort_manifest_path=str(B/'COHORT-MANIFEST.json'),cohort_manifest_sha256=sha(B/'COHORT-MANIFEST.json'),authoritative_ndr_manifest_sha256=plan['ndr_manifest_sha256'],consumer_source_path='lean/PV_EVH_FixtureConsumer.lean',consumer_source_revision='b51b1040f2ffda4a6370a15ea71e5783a16bfa11',consumer_source_sha256=plan['consumer_sha256'],summary=summary,normal_runners=json.load(open(B/'preflight.json'))['runners'],launch_guard_sha256=sha(B/'build.py'))
(B/'READY.json').write_text(json.dumps(ready,indent=2)+'\n');print(json.dumps({k:v for k,v in ready.items() if k!='summary'},indent=2))
