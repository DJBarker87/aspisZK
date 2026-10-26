"""Copy immutable receipts only; no jobs launched or infrastructure changed."""
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next'
h='dombarker@100.108.41.90:';b='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for arg in sys.argv[1:]:
 if arg.isdigit():
  a=int(arg);assert 12800<=a<=13199
  for p in [f'{b}/stage3/{a}-input.json',f'{b}/stage3/{a}.lean.txt',f'{t}/out-{a}.log',f'{t}/time-{a}.log',f'{b}/native-drop/lean/{a}-admission-before.json',f'{b}/native-drop/lean/{a}-admission-barrier.json']:
   subprocess.run(['scp',h+p,str(e)],check=True)
 else:
  assert arg.startswith('success-') and '/' not in arg
  o=e/'translation'/arg;o.mkdir(parents=True,exist_ok=True)
  for name in ['receipt.json','preflight.json','stdout.log','stderr.log','time.log','reservation-at-barrier.json']:
   subprocess.run(['scp',h+f'{b}/src/receipts/{arg}/{name}',str(o)],check=True)
