"""Execute the remaining explicitly authorized dependency chunks sequentially."""
import pathlib,json,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10'
for i in range(6):
 a=40400+i;p=E/f'receipt-{a}.json'
 if p.exists():
  assert json.load(open(p))['accepted'],f'failed chunk {a}: isolate, never rerun unchanged'
 else:
  q=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume10-chunks.py'),str(a),str(i)])
  if q.returncode:sys.exit(q.returncode)
 subprocess.run(['git','add','--',str(E.relative_to(R))],check=True)
 subprocess.run(['git','commit','-m',f'Record native dependency chunk {a}'],check=True)
