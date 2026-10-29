"""Record the exact rejection prefix; no execution or whole-body refinement claimed."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin56-20261029'
paths=['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-core/src/r0/domain.rs','crates/aspis-core/src/r0/mod.rs','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryDomain.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PublishSkeleton54.lean']
texts=[(R/p).read_text() for p in paths]
assert 'pub const FIBRE_COUNT: usize = 1 << 18;' in texts[2]
assert 'index_type!(FibreIndex, FIBRE_COUNT);' in texts[1]
assert 'if index < $bound {\n                    Ok(Self(index))\n                } else {\n                    Err(Error::IndexOutOfRange)' in texts[1]
assert 'while i<22 {\n        let u=FibreIndex::new(queries[i] as usize).unwrap();' in texts[0]
assert 'let i1 ← Array.index_usize queries i\n    let i2 ← Aeneas.Std.lift (UScalar.cast .Usize i1)\n    let r ← aspis_core.r0.domain.FibreIndex.new i2\n    let u ←\n      unwrapSlice r' in texts[3]
assert '| .Err _ => .fail .panic' in texts[3]
assert 'if i < 262144#usize then .ok (.Ok i) else .ok (.Err .IndexOutOfRange)' in texts[4]
rec=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),kind='read-only rejection-prefix source check; Lean source-model counterexample, not a native differential or complete Rust refinement',first_query=262144,valid_fibre_upper_bound_exclusive=1<<18,actual_source_result='index constructor Err(IndexOutOfRange), unwrap panic before any opening read',model_result='Result.fail Error.panic',fixed_link_definitions_unchanged=True,files=[dict(path=p,sha256=hashlib.sha256((R/p).read_bytes()).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip()) for p in paths])
(E/'source-rejection-finding.json').write_text(json.dumps(rec,indent=2)+'\n')
print('Rejection prefix matches: source guard, bound, cast, unwrap and emitted failure branch')
