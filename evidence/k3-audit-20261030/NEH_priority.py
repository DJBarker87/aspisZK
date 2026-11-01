from NEH_replay import *
rows=json.loads((E/'NEH_PRIORITY_NDH.json').read_text()); rows.sort(key=lambda r:(-len([v for v in r['rows'] if v.startswith('NEB:')]),r['receipt']))
# Positive and paired negative stay adjacent; K001 was already run as K030.
rows.sort(key=lambda r:r['receipt'])
for i,r in enumerate(rows):
 a=f'NEH_K{30+i:03}'
 if (E/a/'receipt.json').exists():continue
 rp=r['receipt'];patch=str(Path(rp).parent/'NDH_harness.patch')
 with (E/(a+'-driver.log')).open('w') as f:
  z=subprocess.run([sys.executable,str(E/'NEH_replay.py'),a,rp,patch],stdout=f,stderr=subprocess.STDOUT)
 print(a,rp,z.returncode,flush=True)
 if z.returncode:raise SystemExit('own input fault or migration needed; inspect')
 old=json.loads((ROOT/rp).read_text());t=(E/a/'stdout.log').read_text()
 verdict='OPEN' if ('timed out' in t.lower() or 'timeout' in t.lower() and 'VERIFICATION:- SUCCESSFUL' not in t) else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in t else 'FAIL' if 'VERIFICATION:- FAILED' in t else 'OPEN'
 with (E/'NEH_REPLAY_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=rp,verdict=verdict,expected='PASS' if old['exit_status']==0 else 'FAIL'))+'\n')
 if (old['exit_status']==0 and verdict=='FAIL') or (old['exit_status']!=0 and verdict=='PASS'):
  with (E/'NEH_FINDINGS.md').open('a') as f:f.write(f'\nImmediate replay finding: {a} / {rp}: expected historical exit {old["exit_status"]}, got {verdict}. Credit WITHDRAWN pending precise row consequences.\n')
