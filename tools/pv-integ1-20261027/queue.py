from pathlib import Path
import subprocess,json,sys,time
E=Path('evidence/pv-integ1-20261027');mods=sys.argv[1:]
for m in mods:
 for retry in range(10):
  n=json.loads((E/'TALLY.json').read_text())['next_env_j_id'] if (E/'TALLY.json').exists() else 53900
  r=subprocess.run(['python3','tools/pv-integ1-20261027/lean.py',str(n),m])
  if r.returncode==78:
   for _ in range(3):print('reservation cooldown: 60 seconds',flush=True);time.sleep(60)
   continue
  if r.returncode:sys.exit(r.returncode)
  break
 else:sys.exit(78)
