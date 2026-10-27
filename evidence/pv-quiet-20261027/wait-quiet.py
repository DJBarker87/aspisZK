from pathlib import Path
import time,json,subprocess,sys
from run import H
start=time.time(); receipts=[]
while True:
 label=f'quiet-wait-{len(receipts):02d}'
 code=subprocess.run(['python3',str(H/'quiet-preflight.py'),str(H/(label+'.json'))],stdout=subprocess.DEVNULL).returncode
 cgls=subprocess.run(['systemd-cgls','--user','--no-pager'],text=True,capture_output=True)
 (H/(label+'.cgls.txt')).write_text(cgls.stdout+cgls.stderr)
 receipts.append(dict(utc=time.time(),elapsed=time.time()-start,exit=code,guard=label+'.json'))
 (H/'quiet-wait.json').write_text(json.dumps(dict(start=start,receipts=receipts),indent=2))
 if code==0:sys.exit(0)
 if time.time()-start>=900:sys.exit(78)
 time.sleep(min(30,max(0,900-(time.time()-start))))
