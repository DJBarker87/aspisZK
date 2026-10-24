"""Read-only postrun supplemental binary/artifact identities; never a prior gate."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
files=list((D/'target').rglob('*.out'))+list((D/'target').rglob('*.symtab.json'))
files += [Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')/s for s in ['charon','charon-driver']]
out=dict(schema='ProverRwFactoryCleanup-postrun-v1',assessment='Postrun identities only. charon-driver was not pinned before extraction049; this does not repair that missing preflight identity. Generated Kani objects are not native release binaries.',files=[dict(path=str(p),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files],print_axioms='N/A: read-only hashing')
(D/'postrun-artifacts.json').write_text(json.dumps(out,indent=2)+'\n')
print('hashed',len(files),'postrun files')
