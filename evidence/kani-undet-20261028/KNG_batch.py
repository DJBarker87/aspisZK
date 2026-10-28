from KNG_control import *
for n in ['KNG_gate.py','KNG_metadata.py']:
 text=(E/n).read_text();r=py(f'from pathlib import Path;Path({B+"/"+n!r}).write_text({text!r})');assert r.returncode==0,r.stderr
plan=json.loads((E/'KNG_RUN_PLAN.json').read_text())
sources=['KNG_gate.py','KNG_metadata.py','KNG_src/Cargo.lock','KNG_src/Cargo.toml','KNG_src/crates/aspis-core/src/field.rs','KNG_src/crates/aspis-r1-cost-probe/Cargo.toml','KNG_src/crates/aspis-statement/Cargo.toml']
for c in ['aspis-statement','aspis-r1-cost-probe']:sources+=['KNG_src/crates/'+c+'/src/lib.rs','KNG_src/crates/'+c+'/src/KNG_KMX_stubs.rs']
for n in ['pair_terminal','pair_tree_profile','pair_forest_terminal']:sources+=['KNG_src/crates/aspis-statement/src/pool_v1/'+n+'.rs']
for n in ['KNG_NBH_after','KNG_NBH_live','KNG_NBU_more','KNG_NBU_decode']:sources+=['KNG_src/crates/aspis-statement/src/pool_v1/'+n+'.rs']
sources+=['KNG_src/crates/aspis-r1-cost-probe/src/KNG_LPi_contracts.rs']
start=int(sys.argv[1]) if len(sys.argv)>1 else 1;end=int(sys.argv[2]) if len(sys.argv)>2 else 52
for idx,row in enumerate(plan):
 for neg in [False,True]:
  number=idx*2+int(neg)+1
  if not start<=number<=end:continue
  a=f'KNG_K{number:03}';crate=row['crate'];h=row['control' if neg else 'positive']
  meta=json.loads((E/('KNG_I005' if crate=='aspis-r1-cost-probe' else 'KNG_I006')/'stdout.log').read_text())
  rc=launch(a,'kani',['python3','KNG_gate.py',a,crate,h],sources,meta['resolved_features_per_crate'])
  r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in [{a+'-metadata.json'!r},{a+'-gate.json'!r}] if (b/n).exists()}}))''');assert r.returncode==0,r.stderr
  for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
  log=(E/a/'stdout.log').read_text();gp=E/(a+'-gate.json');g=json.loads(gp.read_text()) if gp.exists() else None
  rc.update(historical_attempt=row['historical_attempt'],harness=h,role='matched_negative' if neg else 'positive',rule14_quarantine=False,gate=g,metadata_root_explanation='Isolated metadata-only dependency root, including statement root dev dependencies; every edge/package/checksum checked against frozen compilation lock. Wrapper excluded from deployed source.')
  (E/a/'receipt.json').write_text(json.dumps(rc,indent=2)+'\n')
  print(a,row['historical_attempt'],h,rc['exit_status'],rc['wall_seconds'],flush=True)
  if 'error[' in log or 'could not compile' in log or 'VERIFICATION' not in log:
   print(log[-5000:],flush=True);raise SystemExit('STOP own compile/gate error; fix inputs before new attempt')
  if neg and rc['exit_status']==0:raise SystemExit('STOP matched negative passed')
