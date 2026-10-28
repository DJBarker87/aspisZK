from pathlib import Path
import json,hashlib,sys,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');name=sys.argv[1];package=sys.argv[2]
out=D/name;out.mkdir(exist_ok=True);assert not (out/'source-manifest.json').exists()
rows=[]
for p in D.rglob('*'):
 if not p.is_file() or any(x in p.relative_to(D).parts for x in ['target','tmp-Kani','lean-objects']):continue
 if p.suffix not in ['.rs','.toml','.lock']:continue
 rows.append(dict(path=str(p.relative_to(D)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(out/'source-manifest.json').write_text(json.dumps(rows,indent=2))
for rel in ['KMX_stubs.rs',package+'/lib.rs' if package not in ['split','native/core'] else package+'/src/sealed.rs' if package=='split' else package+'/src/field/wide_exact.rs']:
 p=D/rel;shutil.copyfile(p,out/(p.name+'.txt'))
