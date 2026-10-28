"""Structural K-1 substitute: bind the owned reference to frozen lane_root."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028'
p=R/'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs';ref=R/'tools/pv-runjoin31-20261028/lane-reference.rs'
s=p.read_text();a=s.index('fn lane_root(');b=s.index('\nfn temporary_context',a);body=s[a:b]
r=ref.read_text();c=r.index('pub fn lane_root(');d=r.index('\n// Retain',c);owned=r[c:d]
# Whitespace only is ignored; the helper expansion is checked exactly.
flat=lambda s:re.sub(r'\s+','',s)
expected=body.replace('fn lane_root','pub fn lane_root',1).replace('input: &PoolV1PairInputNoteWitnessV1','input: PoolV1PairInputNoteWitnessV1')
old='''current = if ((input.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };'''
assert old in expected
expected=expected.replace(old,'current = step(current, sibling, ((input.membership.index >> level) & 1) != 0);')
loop='for level in 0..20 {\n        let sibling = input.membership.siblings[level];\n        current = step(current, sibling, ((input.membership.index >> level) & 1) != 0);\n    }'
assert loop in expected
expected=expected.replace(loop,'\n'.join(f'current = step(current, input.membership.siblings[{n}], ((input.membership.index >> {n}) & 1) != 0);' for n in range(20)))

assert flat(owned)==flat(expected)
step='''pub fn step(current: Digest, sibling: Digest, reverse: bool) -> Digest {
    if reverse { pool_v1_tree_parent(&sibling, &current) }
    else { pool_v1_tree_parent(&current, &sibling) }
}'''
assert flat(step) in flat(r)
row=dict(evidence_class='structural (K-1 substitute)',source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),reference_path=str(ref.relative_to(R)),reference_sha256=hashlib.sha256(ref.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),same_error_map=True,same_loop_range=True,same_index_and_sibling_order=True,differences=['fixed 0..20 loop unrolled in increasing order, no early loop exits','Copy input passed by value instead of shared reference; fields read without writes','conditional two-parent expression moved to owned step helper; guard complemented and branches exchanged'],lean_obligation='step Boolean branch equality, then complete Result induction through unchanged 20 levels',native_validation='pending; no completed native link claimed')
(E/'lane-structural.json').write_text(json.dumps(row,indent=2)+'\n');print('checked exact lane-root helper substitution and all remaining source tokens')
