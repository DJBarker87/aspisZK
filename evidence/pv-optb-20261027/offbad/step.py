"""Append one proof step and check the smallest changed module."""
import pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path('docs/research/v8-r0-zk-20261009/lean')
def nextid():return max([44599]+[int(f.stem[7:]) for f in P.glob('launch-*.json')])+1
def check(module):
 a=nextid();r=subprocess.run(['python3',str(P/'check.py'),str(a),module],capture_output=True,text=True)
 print(a,module,r.returncode,r.stdout[-3500:] if r.returncode else 'checked',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
def append(module,ns,name,body):
 p=ROOT/(module+'.lean');p.write_text(p.read_text().replace('end '+ns,body+'\n#print axioms '+name+'\nend '+ns));check(module)
