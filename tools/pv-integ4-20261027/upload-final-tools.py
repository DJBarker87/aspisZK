from pathlib import Path
import subprocess,sys
D='/home/dombarker/project-offloads/codex-pv-integ4-20261027';P=Path(__file__).resolve().parent
payload={n:(P/n).read_text() for n in ['build-batch1-cost.py','verify-batch1.py','audit-corpus.py']}
code=f'''from pathlib import Path
import subprocess,json,hashlib,sys
D=Path({D!r});O=D/{sys.argv[1]!r};O.mkdir()
r=subprocess.run(['python3',str(D/'reservation.py'),str(O/'admission.json')],stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
(O/'exit.json').write_text(json.dumps({{'exit':r.returncode}}))
if r.returncode or not json.loads((O/'admission.json').read_text()).get('allowed',False):sys.exit(r.returncode or 78)
payload={payload!r}
for n,s in payload.items():
 p=D/n;assert not p.exists();p.write_text(s)
(O/'pins.json').write_text(json.dumps({{n:hashlib.sha256(s.encode()).hexdigest() for n,s in payload.items()}},indent=2))
'''
raise SystemExit(subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True).returncode)
