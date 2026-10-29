"""Read-only final cohort audit; READY records success or the exact stop."""
from pathlib import Path
import json,hashlib,time
B=Path(__file__).resolve().parent;E=B/'resume3'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.load(open(B/'plan.json'));pre=json.load(open(E/'first-root-preflight.json'))
for name,digest in json.load(open(B/'preflight.json'))['runners'].items():assert sha(B/name)==digest,('normal runner changed',name)
receipts=[json.load(open(p)) for p in sorted(B.glob('lean-*/receipt.json')) if p.parent.name!='lean-71000']
success=[r for r in receipts if r['exit_status']==0]
for r in receipts:
 assert set(r['source_hashes'].values())=={plan['sources'][r['module']]['sha256']},('source pin mismatch',r['attempt'])
lean_hashes=sorted({r['deps_fingerprint']['lean_binary_sha256'] for r in receipts})
assert len(lean_hashes)<=1,('toolchain drift',lean_hashes)
complete={r['module'] for r in success}==set(plan['rebuild']) and len(success)==510 and len(receipts)==510 and not (E/'STOP.json').exists()
roots=list(map(Path,pre['LEAN_PATH'].split(':')))
def resolve(m):
 top=m.split('.')[0];root=next(r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file())
 return root/(m.replace('.','/')+'.olean')
summary=dict(modules_rebuilt=len(success),modules_planned=510,mechanical_attempts=len(receipts),proof_attempts=0,precompiler_guard_refusals=[71001],lean_binary_sha256=lean_hashes[0] if lean_hashes else None,prior_environment_failure=71000,reservation_refusals=[json.load(open(p)) for p in sorted(E.glob('refusal-*.json'))],compile_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max([int(r['peak_rss_kib']) for r in receipts]+[0]),swaps=sum(int(r['swaps']) for r in receipts),source_revision='5098cacee75c803ba0486836a94c9894afbafab4',attempts=[r['attempt'] for r in receipts],consumer_compile_run=False,consumer_axioms='not run: aggregation not authorized',print_axioms={r['module']:r['print_axioms'] for r in receipts})
summary['overlay_wall_seconds']=pre['wall_seconds']
finished=[l for l in (E/'build.log').read_text().splitlines() if l.startswith('STAGE1 BUILDS COMPLETE ')]
summary['build_loop_wall_seconds']=float(finished[-1].split()[-1]) if finished else None
manifest=None
if complete:
 assert all(r['swaps']=='0' and int(r['peak_rss_kib'])<=7*1024*1024 and r['wall_seconds']<600 for r in receipts)
 rows=[]
 for v in pre['entries']:
  m=v['module'];p=resolve(m);assert str(p)==v['path'],m
  if m not in plan['rebuild']:assert sha(p)==v['sha256'],m
  q=dict(module=m,path=str(p),sha256=sha(p),kind='reconciled rebuild' if m in plan['rebuild'] else v['kind'],companions=[])
  for c in [Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]:
   if c.exists():q['companions'].append(dict(path=str(c),sha256=sha(c),bytes=c.stat().st_size))
  if m not in plan['rebuild']:
   assert q['companions']==v['companions'],('companion changed',m)
  assert not p.is_symlink()
  rows.append(q)
 manifest=dict(authoritative_cohort='NDR',authoritative_manifest_sha256=plan['ndr_manifest_sha256'],LEAN_PATH=pre['LEAN_PATH'],first_root_preflight_sha256=sha(E/'first-root-preflight.json'),entries=rows,rebuild=plan['rebuild'],reuse=plan['reuse'])
 (E/'COHORT-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
ready=dict(status='READY FOR LEAD REVIEW; STOP BEFORE AGGREGATION' if complete else 'NOT READY: STOPPED DURING RECONCILIATION',stage1_complete=complete,aggregation_authorized=False,aggregation_run=False,LEAN_PATH=pre['LEAN_PATH'],cohort_manifest_path=str(E/'COHORT-MANIFEST.json') if complete else None,cohort_manifest_sha256=sha(E/'COHORT-MANIFEST.json') if complete else None,authoritative_ndr_manifest_sha256=plan['ndr_manifest_sha256'],consumer_source_path='lean/PV_EVH_FixtureConsumer.lean',consumer_source_sha256=plan['consumer_sha256'],first_root_preflight_sha256=sha(E/'first-root-preflight.json'),launch_guard_sha256=sha(B/'build3.py'),normal_runners=json.load(open(B/'preflight.json'))['runners'],summary=summary,prior_environment_failure=dict(attempt=71000,failure_class='pre-elaboration root-shadowing',correction='D513 namespace-complete plain-copy overlay; u-prime; fresh IDs'),stop=json.load(open(E/'STOP.json')) if (E/'STOP.json').exists() else None)
(E/'READY.json').write_text(json.dumps(ready,indent=2)+'\n')
print(json.dumps({k:v for k,v in ready.items() if k!='summary'},indent=2))
