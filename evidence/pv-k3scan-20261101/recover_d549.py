from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent
path='/home/dombarker/project-offloads/codex-pv-kscan-20261028/d347/D038/updates.json'
b=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+path]);d=json.loads(b)
(E/'D038-updates.json.xz').write_bytes(lzma.compress(b,preset=6));(E/'D038-updates.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
print(len(d),'snapshot entries',len(b),'bytes')
for n,t in d.items():
 if n.endswith(('Cargo.toml','build.rs','src/lib.rs')) and any(s in n for s in ['cost-probe','core/','statement/']):print(n,hashlib.sha256(t.encode()).hexdigest(),len(t))
