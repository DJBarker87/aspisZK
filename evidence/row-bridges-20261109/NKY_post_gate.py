from pathlib import Path
import subprocess,sys,time,os,json
E=Path(__file__).resolve().parent;pid=int(sys.argv[1])
while True:
 try:os.kill(pid,0)
 except ProcessLookupError:break
 time.sleep(1)
assert json.loads((E/'NKY_L068/receipt.json').read_text())['exit_status']==0,'Final pin/export failed; do not launch dependent work'
assert not (E/'NKY_CLIENT_ACTIVE').exists()
r=subprocess.run([sys.executable,str(E/'NKY_run.py'),'NKY_L069','audit','review-close']);assert r.returncode==0
r=subprocess.run([sys.executable,str(E/'NKY_cleanup_stage.py')]);assert r.returncode==0
print('focused statement inventory and controlled native cleanup assertions complete',flush=True)
