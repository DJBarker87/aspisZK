from NEH_replay import *
from NEH_migrate_common import migrate
c=json.loads((ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json').read_text())[0]
pairs=list(zip(c['kani_receipt_paths'],c['control_receipts']))
# Pair each same-property falsification immediately after its native observation.
for i,rp in enumerate([v for pair in pairs for v in pair]):
 a=f'NEH_K{72+i:03}'
 if (E/a/'receipt.json').exists():continue
 out=migrate(rp);patch=str(Path(rp).parent/'NDM_harness.patch')
 with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NEH_replay.py'),a,rp,patch],env={**os.environ,'NEH_OVERLAY_FILE':str(out)},stdout=f,stderr=subprocess.STDOUT)
 print(a,rp,r.returncode,flush=True)
 if r.returncode:raise SystemExit('own input fault or migration needed; inspect')
 t=(E/a/'stdout.log').read_text();v='OPEN' if ('timed out' in t.lower() or 'timeout' in t.lower() and 'VERIFICATION:- SUCCESSFUL' not in t) else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in t else 'FAIL' if 'VERIFICATION:- FAILED' in t else 'OPEN';old=json.loads((ROOT/rp).read_text())
 with (E/'NEH_REPLAY_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=rp,verdict=v,expected='PASS' if i%2==0 else 'FAIL',method=json.loads(out.with_name(out.name.replace('_local','_migration')).read_text())['method']))+'\n')
 if (i%2==0 and v=='FAIL') or (i%2==1 and v=='PASS'):
  with (E/'NEH_FINDINGS.md').open('a') as f:f.write(f'\nImmediate local-record replay finding: {a} / {rp}, {v}; see exact source and receipt. No affected parent credit can be restored.\n')
