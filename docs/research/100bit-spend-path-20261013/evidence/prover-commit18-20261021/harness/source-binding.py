#!/usr/bin/env python3
"""Bind actual source text and harness-only appendages, never assert equivalence."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit18-20261021'
host='dombarker@100.108.41.90'
rows=[]
for rel in ['crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-r1-cost-probe/src/sim.rs','crates/aspis-r1-cost-probe/src/prover.rs']:
 local=Path(rel).read_bytes()
 result=subprocess.run(['ssh',host,'cat '+H+'/src/'+rel],check=True,capture_output=True).stdout
 assert result.startswith(local),rel
 rows.append(dict(source=rel,production_sha256=hashlib.sha256(local).hexdigest(),host_instrumented_sha256=hashlib.sha256(result).hexdigest(),production_prefix_exact=True,appended_bytes=len(result)-len(local)))
(E/'source-binding.json').write_text(json.dumps(dict(production_revision='c35b7b481402f81e2ea5c967c4c61d5b8dc01d5d',rows=rows,claim='Exact source-byte binding only; no probabilistic or semantic equality follows.'),indent=2)+'\n')
