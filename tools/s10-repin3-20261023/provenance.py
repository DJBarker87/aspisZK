#!/usr/bin/env python3
"""Pin retained algorithms, adapters, immutable host helpers and comparison inputs."""
import hashlib,json,shlex,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(T.rglob('*.py')):
 original=R/'tools/s10-repin2-20261023'/p.relative_to(T)
 if original.exists():rows.append(dict(original=str(original.relative_to(R)),original_sha256=sha(original),adapted=str(p.relative_to(R)),adapted_sha256=sha(p),adaptation='Private paths/build labels, H5 expected/discovered hashes and immediate re-pin2 comparison baseline; reporting/check scripts explicitly handle adopted child changes. Full source remains reviewable.'))
(E/'generator-adapters.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
paths=['/home/dombarker/project-offloads/codex-cx-pin-20261020/harness/capped.py','/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/harness/reservation.py','/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/ownership-policy.py','/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/ownership.json','/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/frontier-input.json','/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023/source-inputs.json','/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023/collected/elf-graphs.json','/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023/declaration-owners.jsonl']
code='from pathlib import Path;import hashlib,json;paths='+repr(paths)+';print(json.dumps([dict(path=s,sha256=hashlib.sha256(Path(s).read_bytes()).hexdigest(),bytes=Path(s).stat().st_size) for s in paths]))'
host=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True))
local=[]
for s in ['source-inputs.json','ordering-observations.json','cfg.json','elf-graphs.json','build-manifest.json']:
 p=E.parent/'s10-repin2-20261023'/s;local.append(dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size))
(E/'comparison-provenance.json').write_text(json.dumps(dict(host_inputs=host,comparison_inputs=local,source_revision=json.loads((E/'source-inputs.json').read_text())['source_revision'],scope='Host helper/immutable input pins; comparison is re-pin2, not the historical S4/frozen baseline. Host-only data is not claimed available locally.'),indent=2,sort_keys=True)+'\n')
print('provenance pinned',len(rows),'adapters')
