"""Read-only recovery of the settled pre-submission transport failure."""
from pathlib import Path
import subprocess,time,json
p=Path(__file__).resolve().parent
cmd='cd /home/dombarker/project-offloads/codex-cx-sound-int2-20261025 && ls -ld JHf_TX2_032* JHf_Carrier0* 2>/dev/null; ps -eo pid,args | rg "JHf_Carrier0|JHf_TX2_032"'
for retry in range(3,11):
 print('Waiting60 before transport recovery',retry,flush=True);time.sleep(60)
 try:
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90',cmd],capture_output=True,text=True,timeout=50)
  item=dict(retry=retry,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,time=time.time(),read_only=True)
 except subprocess.TimeoutExpired as e:
  item=dict(retry=retry,exit=255,stderr='read-only SSH timed out at50 seconds',time=time.time(),read_only=True)
 with (p/'JHf_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(item)+'\n')
 print(json.dumps(item),flush=True)
 if item['exit']!=255:
  (p/'JHf_TRANSPORT_RECOVERED.json').write_text(json.dumps(item,indent=2)+'\n');break
else:
 (p/'JHf_TRANSPORT_STOP.json').write_text(json.dumps(dict(reason='Ten consecutive pre-submission/read-only transport failures; no new scope permitted',time=time.time()),indent=2)+'\n')
