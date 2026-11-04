from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;ns=sys.argv[1];a=sys.argv[2]
code=f"from pathlib import Path;import json;b=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-20261104');print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in [b/'NGG_EXTRACTION_PINS.json',*(b/'NGG_extracted'/{ns!r}).rglob('*.lean')]}}))"
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
 if n.endswith('.lean'):
  q=E/Path(n).relative_to('NGG_extracted');q.parent.mkdir(exist_ok=True,parents=True);q.write_text(s)
 else:(E/a/Path(n).name).write_text(s)
print('Collected',ns)
