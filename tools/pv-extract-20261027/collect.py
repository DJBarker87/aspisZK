from pathlib import Path
import subprocess,json,hashlib
E=Path('evidence/pv-extract-20261027');D='/home/dombarker/project-offloads/codex-pv-extract-20261027'
code='''from pathlib import Path
import json,hashlib
D=Path(BASE);r={}
for p in D.iterdir():
 if p.is_dir() and (p.name.startswith(('aeneas-','charon-','build-diagnostic-'))):
  r[p.name]={f.name:f.read_text() for f in p.iterdir() if f.is_file() and f.suffix in ['.json','.log']}
outputs={}
for p in D.glob('*generated/*'):
 if p.is_file():outputs[str(p.relative_to(D))]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
for p in [D/'pipeline/base/src/_build/default/main.exe',D/'pipeline/base/src/Main.ml',D/'PV_Ext_ShippedOp223.llbc',D/'PV_Ext_ShippedOp223Opt.llbc',D/'source/crates/aspis-statement/src/logup.rs',Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/base/src/Main.ml'),Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')]:
 if p.exists():outputs[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
print(json.dumps(dict(runs=r,output_hashes=outputs)))
'''.replace('BASE',repr(D))
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
for name,files in r['runs'].items():
 p=E/name;p.mkdir(exist_ok=True)
 for n,s in files.items():(p/n).write_text(s)
(E/'output-hashes.json').write_text(json.dumps(r['output_hashes'],indent=2)+'\n')
print(len(r['runs']))
