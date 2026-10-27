from pathlib import Path
import subprocess,sys
D='/home/dombarker/project-offloads/codex-pv-integ4-20261027';body=Path(__file__).with_name('count-batch1.py').read_text();label=sys.argv[1]
code=f'''from pathlib import Path
import subprocess,json,hashlib,sys
D=Path({D!r});O=D/{label!r};O.mkdir()
r=subprocess.run(['python3',str(D/'reservation.py'),str(O/'admission.json')],stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
(O/'exit.json').write_text(json.dumps({{'exit':r.returncode}}))
if r.returncode or not json.loads((O/'admission.json').read_text()).get('allowed',False):sys.exit(r.returncode or 78)
p=D/'count-batch1.py';assert not p.exists();p.write_text({body!r})
(O/'input-pins.json').write_text(json.dumps({{'count-batch1.py':hashlib.sha256(p.read_bytes()).hexdigest()}},indent=2))
'''
raise SystemExit(subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True).returncode)
