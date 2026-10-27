"""Retry only refused uploads, respecting all job admission waits."""
from pathlib import Path
import subprocess,sys
from queue_extract import wait_refusal
root=Path(__file__).resolve().parents[2]
kind=sys.argv[1];assert kind in ('kani','reference')
for i in range(10):
 wait_refusal()
 subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/wait_capacity.py')],check=True)
 p=subprocess.run([sys.executable,str(root/f'tools/pv-cblib-20261027/upload_{kind}.py')])
 if p.returncode!=78:sys.exit(p.returncode)
sys.exit(78)
