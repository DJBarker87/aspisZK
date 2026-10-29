"""Check final source reproduction without compiling or changing any accepted source."""
from pathlib import Path
import subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;E=R/'evidence/pv-runjoin52-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
before={p:p.read_bytes() for p in L.glob('PV_RunJoin_*52.lean')}
for n in ['generate-neutral.py','generate-r72.py','generate-owned-tail.py']:
 subprocess.run([sys.executable,str(T/n)],check=True)
changed=[str(p.relative_to(R)) for p,b in before.items() if p.read_bytes()!=b]
for p,b in before.items():
 if p.read_bytes()!=b:p.write_bytes(b)
result=dict(check='final generated sources byte-identical after regeneration',all_match=not changed,changed=changed,source_hashes={str(p.relative_to(R)):hashlib.sha256(b).hexdigest() for p,b in before.items()},accepted_sources_restored_if_needed=True,compilers_launched=0)
(E/'generator-check.json').write_text(json.dumps(result,indent=2)+'\n');assert not changed,changed
print('All',len(before),'current source files unchanged by regeneration')
