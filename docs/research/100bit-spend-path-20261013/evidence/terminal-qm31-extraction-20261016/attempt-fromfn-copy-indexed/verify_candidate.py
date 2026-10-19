#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
BASE=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-f-row-helper/input')
CAND=ROOT/'input'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((BASE/'merged-source-manifest.json').read_text()); meta=json.loads((ROOT/'candidate-source-manifest.json').read_text())
allowed={'src/lib.rs','src/statement/state_only_poseidon.rs','src/statement/pool_v1/pair_forest_semantic_terminal.rs'}
diffs=[]
for row in base['source_files']:
 rel=row['merged_path']; p=CAND/rel
 if not p.is_file(): raise SystemExit('missing pinned candidate source '+rel)
 h=sha(p); expected=next(x['candidate_sha256'] for x in meta['source_files'] if x['merged_path']==rel)
 if h!=expected: raise SystemExit('candidate source hash mismatch '+rel)
 if h!=row['sha256']: diffs.append(rel)
 if rel not in allowed and h!=row['sha256']: raise SystemExit('unexpected changed source '+rel)
if set(diffs)!={'src/statement/state_only_poseidon.rs','src/statement/pool_v1/pair_forest_semantic_terminal.rs'}:
 raise SystemExit('expected exactly two changed source rows, got '+repr(diffs))
rootbase=(BASE/'src/lib.rs').read_bytes(); rootcand=(CAND/'src/lib.rs').read_bytes()
helper=('\n/// Extraction-only safe fixed-array constructor for Copy outputs.\n/// Calls f in increasing index order and threads the FnMut state normally.\n#[inline(always)]\npub(crate) fn array_from_fn_copy<T: Copy, const N: usize>(\n    init: T,\n    mut f: impl FnMut(usize) -> T,\n) -> [T; N] {\n    let mut out = [init; N];\n    let mut i = 0usize;\n    while i < N {\n        out[i] = f(i);\n        i += 1;\n    }\n    out\n}\n').encode()
marker=b'extern crate alloc;\n'
if rootbase.count(marker)!=1 or rootcand!=rootbase.replace(marker,marker+helper): raise SystemExit('root scaffold differs beyond exact helper insertion')
if b'crate::array_from_fn_copy::<_, ' not in (CAND/'src/statement/state_only_poseidon.rs').read_bytes(): raise SystemExit('state caller helper not present')
count=(CAND/'src/statement/state_only_poseidon.rs').read_bytes().count(b'crate::array_from_fn_copy::<_, ')+(CAND/'src/statement/pool_v1/pair_forest_semantic_terminal.rs').read_bytes().count(b'crate::array_from_fn_copy::<_, ')
if count!=18: raise SystemExit('replacement call count mismatch: '+str(count))
if (CAND/'Cargo.lock').read_bytes()!=(BASE/'Cargo.lock').read_bytes(): raise SystemExit('lock changed')
print(json.dumps({'status':'pass','base_revision':base['source_revision'],'base_manifest_sha256':sha(BASE/'merged-source-manifest.json'),'source_file_rows':len(base['source_files']),'changed_source_rows':diffs,'helper_root_base_sha256':sha(BASE/'src/lib.rs'),'helper_root_candidate_sha256':sha(CAND/'src/lib.rs'),'from_fn_replacement_count':count,'lock_unchanged':True},indent=2))
