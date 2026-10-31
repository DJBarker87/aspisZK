from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=(E/'NEG_extracted/NEG_RowIsolated/Funs.lean').read_text();dots=(E/'NEG_extracted/NEG_DotsTypes/Funs.lean').read_text()
checks={
 'row_add_write': 'let row1 ← Array.update row j i3' in rows,
 'row_flush_some_restored': 'next_back im (some limb1)' in rows,
 'row_flush_none_restored': 'next_back im none' in rows,
 'row_flush_back_applied': 'ok (into_iter_back back)' in rows,
 'row_raw_funs_unedited': h(E/'NEG_extracted/NEG_RowIsolated/Funs.lean')==h(E/'NEG_RowIsolated/Funs.lean'),
 'dot_raw_funs_unedited': h(E/'NEG_extracted/NEG_DotsTypes/Funs.lean')==h(E/'NEG_DotsTypes/Funs.lean'),
 'dot_eight_sum_updates': len(re.findall(r'Array.update sums\d* [0-7]#usize',dots))==8,
 'dot_eight_limb_updates':len(re.findall(r'Array.update limbs\d* [0-7]#usize',dots))==8,
 'frozen_shipped_tree':subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs']).returncode==0,
}
assert all(checks.values()),checks
out=dict(checks=checks,qualification='Conservative explicit writeback-pattern scan plus exact emitted-body SHA checks; source identity and the separate native/emitted differential are both required. The row external continuation repair remains explicit.',source_hashes={str(p.relative_to(E)):h(p) for p in [E/'NEG_extracted/NEG_RowIsolated/Funs.lean',E/'NEG_extracted/NEG_DotsTypes/Funs.lean',E/'NEG_RowIsolated/FunsExternal.lean',E/'NEG_DotsTypes/FunsExternal.lean']})
(E/'NEG_DROPPED_RESTORATION_SCAN.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(checks))
