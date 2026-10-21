#!/usr/bin/env python3
"""Read-only check of the actual private-host source/Cargo inputs."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/stored-carrier-20261021'
H='/home/dombarker/project-offloads/codex-cx-stored-carrier-20261021'
paths=[R/'Cargo.toml',R/'Cargo.lock']
for base in ['tools/stored-carrier-kit','tools/r1-builder-reference','crates/aspis-core','crates/aspis-statement','crates/aspis-r1-cost-probe','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon']:
 paths += [p for p in (R/base).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml','.lock'] and 'target' not in p.parts]
paths += [R/'docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs',R/'programs/r1-cost-probe/src/pool_route.rs']
pins={str(p.relative_to(R)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in paths}
script='''from pathlib import Path
import hashlib,json,subprocess
r=Path(%r)
pins=%r
bad=[p for p,v in pins.items() if not (r/p).exists() or hashlib.sha256((r/p).read_bytes()).hexdigest()!=v['sha256']]
tools={}
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),*Path('/home/dombarker/.kani/kani-0.67.0/bin').glob('*')]:
 if p.is_file():tools[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
print(json.dumps(dict(mismatches=bad,checked=len(pins),tools=tools)))
'''%(H,pins)
check=json.loads(subprocess.check_output(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=30','-o','ServerAliveCountMax=3','dombarker@100.108.41.90','python3 -'],input=script,text=True,timeout=120))
result=dict(host=H,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),pins=pins,validation=check,shipped_diff=subprocess.check_output(['git','diff','--name-only','0a7ee2dcc','--','crates','programs'],cwd=R,text=True).splitlines())
(E/'source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
assert not check['mismatches'],check['mismatches'];assert not result['shipped_diff']
print(json.dumps(dict(checked=check['checked'],mismatches=check['mismatches'])))
