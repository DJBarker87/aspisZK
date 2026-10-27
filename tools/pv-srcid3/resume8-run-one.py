#!/usr/bin/env python3
"""Sequential proof-target client with fresh IDs and mandatory refusal waits."""
import pathlib,subprocess,sys,time,json
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
for module in sys.argv[1:]:
 for retry in range(10):
  n=int((e/'resume8-next-id.txt').read_text());assert 41500<=n<=41799
  (e/'resume8-next-id.txt').write_text(str(n+1)+'\n')
  print('START',n,module,flush=True)
  r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume8-compile.py'),str(n),module],capture_output=True,text=True)
  (e/f'client-{n}.log').write_text(r.stdout+r.stderr)
  print('END',n,r.returncode,(r.stdout+r.stderr)[-2400:],flush=True)
  if r.returncode!=78:break
  for _ in range(3):print('reservation wait 60 seconds',flush=True);time.sleep(60)
 else:sys.exit(78)
 if r.returncode:sys.exit(r.returncode)
