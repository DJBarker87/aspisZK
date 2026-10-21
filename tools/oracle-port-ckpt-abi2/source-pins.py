#!/usr/bin/env python3
"""Pin local proof inputs and validate the isolated host snapshot read-only."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-abi2-20261021'
H='/home/dombarker/project-offloads/codex-cx-ckpt-abi2-20261021'
paths=[R/'Cargo.toml',R/'Cargo.lock']
for name in ['aspis-core','aspis-statement','aspis-r1-cost-probe']:
 paths += [R/'crates'/name/'Cargo.toml',*(R/'crates'/name/'src').rglob('*.rs')]
paths += list((R/'tools/r1-builder-reference').rglob('*.rs'))
paths += list((R/'tools/oracle-port-ckpt-abi2/src').glob('*.rs'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in paths}
script='from pathlib import Path\nimport hashlib,json\nr=Path('+repr(H)+')\npins='+repr(pins)+'\nbad=[p for p,v in pins.items() if not (r/p).exists() or hashlib.sha256((r/p).read_bytes()).hexdigest()!=v["sha256"]]\nprint(json.dumps(dict(mismatches=bad,checked=len(pins))))\n'
check=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),pins=pins,host=H,validation=check,shipped_diff=subprocess.check_output(['git','diff','--name-only','ec56a3486','--','crates','programs'],cwd=R,text=True).splitlines())
(E/'source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(check));assert not check['mismatches'];assert not result['shipped_diff']
