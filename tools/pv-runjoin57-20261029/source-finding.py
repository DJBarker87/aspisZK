"""Inspect the failed read prefix; no complete source refinement is claimed."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin57-20261029'
paths=['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/host_commitment.rs','crates/aspis-core/src/r0/domain.rs','crates/aspis-core/src/r0/mod.rs','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryDomain.lean']
s=[(R/p).read_text() for p in paths]
assert 'pub const FIBRE_COUNT: usize = 1 << 18;' in s[3]
assert 'index_type!(FibreIndex, FIBRE_COUNT);' in s[2]
assert 'let u=FibreIndex::new(queries[i] as usize).unwrap();' in s[0]
assert 'cc1.fill_opening(u,&mut opening);cc2.fill_opening(u,&mut opening);' in s[0]
assert 'out.values=fill_opening_values(self,u,out.values,0);' in s[1]
assert 'let lane=c.lanes[j];\n    let row=opening_lane_values(&c.words[j],u);' in s[1]
assert 'let w ←\n      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice\n        host_commitment.Word) c.words j' in s[4]
assert s[4].index('let w ←\n      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice\n        host_commitment.Word) c.words j') < s[4].index('let row ← host_commitment.opening_lane_values w u')
rec=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),evidence_class='Lean source-model failure plus read-only source-prefix inspection; no native differential or complete Rust refinement',queries='22 zero indices; every value <262144',commitment='time C1, lanes=[0], words=[], arbitrary tree, no salts',native_prefix='FibreIndex(0) accepted; lane[0] exists; words[0] bounds panic',model_prefix='Result.fail Error.arrayOutOfBounds before opening_lane_values and before any mutable-borrow update',interpretation='Admitted by Fields and QueryRange; not asserted reachable from an honest finish_opening',deployed_configuration='Existing source cohort retained; reached failure prefix has no feature/profile conditional. No new extraction, Rust execution or deployed-code credit claimed.',files=[dict(path=p,sha256=hashlib.sha256((R/p).read_bytes()).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip()) for p in paths])
(E/'source-finding.json').write_text(json.dumps(rec,indent=2)+'\n')
print('Checked zero-index and missing-word source prefix')
