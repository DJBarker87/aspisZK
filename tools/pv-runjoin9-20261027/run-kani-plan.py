#!/usr/bin/env python3
"""Run the six prelisted independent leaves sequentially, respecting admission waits."""
import json,pathlib,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin9-20261027'
for number in range(int(sys.argv[1]),7):
 for retry in range(11):
  r=subprocess.run([sys.executable,str(root/'tools/pv-runjoin9-20261027/kani.py'),str(number),str(retry)],capture_output=True,text=True)
  (e/f'kani-driver-{number:02d}-{retry}.log').write_text(r.stdout+r.stderr)
  if r.returncode==78:
   print('Kani reservation refused',number,retry,flush=True)
   if retry==10:sys.exit(78)
   with (e/'kani-waits.jsonl').open('a') as f:f.write(json.dumps(dict(number=number,retry=retry,seconds=180))+'\n')
   until=time.time()+180
   while time.time()<until:time.sleep(min(30,until-time.time()))
   continue
  p=e/f'pv9-runjoin-kani-{number:02d}/receipt.json'
  x=json.loads(p.read_text()) if p.exists() else {}
  print('KANI RESULT',json.dumps({k:x.get(k) for k in ['number','harness','exit','wall_seconds','peak_rss_bytes','swaps']}),flush=True)
  if r.returncode:
   print(r.stdout[-3000:]+r.stderr,flush=True);sys.exit(r.returncode)
  break
