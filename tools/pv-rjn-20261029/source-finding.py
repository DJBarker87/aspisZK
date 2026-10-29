"""Read-only inspection of the frozen Rust rejection prefix; no native credit."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjn-20261029'
base='c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7'
paths=['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/host_tree.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','crates/aspis-r1-cost-probe/src/compact.rs','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean']
files={p:subprocess.check_output(['git','show',base+':'+p]) for p in paths}
prover=files[paths[0]].decode();tree=files[paths[1]].decode();mp=files[paths[2]].decode();compact=files[paths[3]].decode()
checks={
 'source_index_rejection':'indices[i]>=1<<LEAF_BITS' in tree,
 'check_before_count_copy':tree.index('check_indices(indices)?;')<tree.index('level[..indices.len()].copy_from_slice(indices);'),
 'count_before_tree_walk':tree.index('let count=node_count(indices)?;')<tree.index('let out=multiproof_levels(self,out,level,0,bits);'),
 'first_slot_is_c1_batch0':'let out=append_node_slot(out,cc1,cc2,tree,queries,0,0)?;' in prover,
 'native_error_allocation':'.ok_or(Error::Allocation)?' in prover,
 'LEAF_BITS_18':'LEAF_BITS: u32 = 18' in mp or 'LEAF_BITS:u32=18' in mp.replace(' ',''),
 'MAX_BATCH_16':'MAX_BATCH: usize = 16' in mp or 'MAX_BATCH:usize=16' in mp.replace(' ',''),
 'SPLIT_10':'SPLIT:usize=10' in compact.replace(' ','') or 'SPLIT:usize=10' in compact.replace(' ',''),
}
assert all(checks.values()),checks
out=dict(base=base,evidence_class='source-model obstruction plus read-only Rust failure-prefix inspection',checks=checks,
 files=[dict(path=p,revision=base,git_blob=subprocess.check_output(['git','rev-parse',base+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),size=len(b)) for p,b in files.items()],
 mutation_fidelity='The rejection prefix ends before node_count copies indices or multiproof_levels accesses tree memory. The proof obtains publication_indices success from the NodeAppend link under refutation; it does not assert a separately proved generic source law for that insertion loop.',
 retained_boundary='No new source-to-model refinement, deployed execution, compiler-preservation, extraction, native differential, ELF or privacy credit.')
(E/'source-finding.json').write_text(json.dumps(out,indent=2)+'\n');print(checks)
