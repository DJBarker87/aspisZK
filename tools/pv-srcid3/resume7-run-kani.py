#!/usr/bin/env python3
import pathlib,subprocess,time,json,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
for level in (sys.argv[1:] or ['prefix11','suffix10']):
 harness='pool_v1::pair_forest_copy_builder::records_proofs::empty_roots::pv_srcid7_helper_'+level
 ledger=e/'resume7-kani-invocations.jsonl'
 prior=[json.loads(x) for x in ledger.read_text().splitlines()] if ledger.exists() else []
 if any(r['harness']==harness for r in prior):continue
 for retry in range(10):
  name='srcid7-root'+level+'-try'+str(retry)
  if (e/('reservation-'+name+'.json')).exists() or (e/('local-reservation-hold-'+name+'.json')).exists():continue
  with (e/(name+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(root/'tools/pv-srcid3/resume7-kani.py'),name,harness,'180'],stdout=f,stderr=subprocess.STDOUT)
  print(name,r.returncode,flush=True)
  if r.returncode!=78:break
  for _ in range(3):time.sleep(60)
 else:sys.exit(78)
 out=e/name/'stdout.log'
 if out.exists() and ('VERIFICATION:- FAILED' in out.read_text() or 'VERIFICATION FAILED' in out.read_text()):sys.exit(1)
