#!/usr/bin/env python3
"""Pin the diagnosed branch; no claim of a whole-function proof."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parents[2]
rust=root/'crates/aspis-r1-cost-probe/src/candidate.rs'
lean=root/'docs/research/100bit-spend-path-20261013/lean/Port3_NativeBatchBody.lean'
r=rust.read_text();l=lean.read_text()
checks={
 'rust_padding_parse': 'return Err(Error::Parse);' in r[r.index('if count > SLOT_NODES[s]'):r.index('if !multiproof::verify_in_place')],
 'emitted_padding_none': 'if b\n        then ok (done (idx, val, none))' in l,
 'emitted_count_none': 'if val1 > i\n      then ok (done (idx, val, none))' in l,
 'emitted_verify_none': 'else ok (done (idx1, val2, none))' in l,
 'emitted_decoder_panic': 'match pending_return with\n  | none => fail panic\n  | some r => ok (r, idx1, val1)' in l,
}
assert all(checks.values()),checks
out={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'checks':checks,'files':{str(p.relative_to(root)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in [rust,lean]},
 'scope':'Literal branch audit plus separately checked branch-carrier theorem. Not a whole native execution counterexample or a proof of admitted reachability.'}
(root/'evidence/port4b-20261023/source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(checks))
