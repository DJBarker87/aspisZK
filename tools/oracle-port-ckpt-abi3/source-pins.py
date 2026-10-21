#!/usr/bin/env python3
"""Pin source/Cargo inputs and check the isolated host without building."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-abi3-20261021'
H='/home/dombarker/project-offloads/codex-cx-ckpt-abi3-20261021'
paths=[R/'Cargo.toml',R/'Cargo.lock',R/'tools/oracle-port-ckpt-abi3/Cargo.toml',R/'tools/oracle-port-ckpt-abi3/Cargo.lock']
for name in ['aspis-core','aspis-statement','aspis-r1-cost-probe']:
 paths += [R/'crates'/name/'Cargo.toml',*(R/'crates'/name/'src').rglob('*.rs')]
for d in ['tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon']:
 paths += list((R/d).rglob('*.rs'))
 paths += list((R/d).rglob('Cargo.toml'))
paths += list((R/'tools/oracle-port-ckpt-abi3/src').glob('*.rs'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in paths}
script='from pathlib import Path\nimport hashlib,json\nr=Path('+repr(H)+')\npins='+repr(pins)+'\nbad=[p for p,v in pins.items() if not (r/p).exists() or hashlib.sha256((r/p).read_bytes()).hexdigest()!=v["sha256"]]\nprint(json.dumps(dict(mismatches=bad,checked=len(pins))))\n'
check=json.loads(subprocess.check_output(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -'],input=script,text=True,timeout=120))
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),pins=pins,host=H,validation=check,shipped_diff=subprocess.check_output(['git','diff','--name-only','6881031b8','--','crates','programs'],cwd=R,text=True).splitlines())
(E/'source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(check));assert not check['mismatches'];assert not result['shipped_diff']
