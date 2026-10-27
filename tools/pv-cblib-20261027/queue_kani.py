from pathlib import Path
import subprocess,sys
from queue_extract import wait_refusal
root=Path(__file__).resolve().parents[2]
label,harness,project=sys.argv[1:4]
for i in range(1,11):
 wait_refusal()
 subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/wait_capacity.py')],check=True)
 p=subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/kani.py'),f'{label}-r{i:02}',harness,project])
 if p.returncode!=78:sys.exit(p.returncode)
sys.exit(78)
