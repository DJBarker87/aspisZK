#!/usr/bin/env python3
"""Run the six named new mapper splits sequentially, preserving refusal receipts."""
import pathlib,subprocess,sys,time,json
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
prefix='pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::'
for variant in ['transfer','withdrawal']:
 for part in ['fields','path','public']:
  harness=prefix+'pv_srcid5_'+variant+'_'+part
  f=e/'resume5-kani-invocations.jsonl';prior=[json.loads(x) for x in f.read_text().splitlines()] if f.exists() else []
  if any(r['harness']==harness for r in prior):continue
  for retry in range(10):
   name=f'srcid5-{variant}-{part}-try{retry}'
   if (e/f'reservation-{name}.json').exists() or (e/f'local-reservation-hold-{name}.json').exists():continue
   print('START',name,harness,flush=True)
   r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume5-kani.py'),name,harness,'180'],capture_output=True,text=True)
   (e/f'{name}-client.log').write_text(r.stdout+r.stderr)
   print('END',name,r.returncode,(r.stdout+r.stderr)[-1800:],flush=True)
   if r.returncode!=78:break
   for _ in range(3):print('reservation wait 60 seconds',flush=True);time.sleep(60)
  else:sys.exit(78)
  # A verification timeout is not repeated: next target is a different split.
  # Stop only for a checked counterexample, retaining the exact failing claim.
  out=e/name/'stdout.log'
  if out.exists() and ('VERIFICATION:- FAILED' in out.read_text() or 'VERIFICATION FAILED' in out.read_text()):
   print('CHECKED FAILURE: inspect before further work',flush=True);sys.exit(1)
