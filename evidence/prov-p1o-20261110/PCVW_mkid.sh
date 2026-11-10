#!/bin/bash
# usage: bash PCVW_mkid.sh RUN [TIMEOUT]   statement chain of P1l PCVT_E014 at the pin (jobs 1, stager -Zthreads=1), namespace PCVT_stmG
cd "$(dirname "$0")"
RUN=$1;TMO=${2:-180}
MANIFEST=crates/aspis-statement/Cargo.toml JOBS=1 bash PCVW_mkspec2.sh "$RUN" original PCVT_stmG "crate::logup::compress_tagged_tuple,crate::pool_v1::pair_forest_semantic_terminal::r0::_::public_bytes,crate::constraints_v4::sparse_eq_weights,crate::pool_v1::pair_tree_hiding::build_pool_v1_pair_copy_row_schedule_v1,crate::state_only_poseidon::internal_linear_lazy" "crate::pool_v1::pair_tree_hiding::endpoint_counts" "r0,pool-v1-kernel" stmtG
python3 -B - "$RUN" "$TMO" <<'PY'
import json,sys
run,tmo=sys.argv[1],int(sys.argv[2]);f=run+'_spec.json';d=json.load(open(f))
d['timeout']=tmo
d['fingerprint_dir']='/home/dombarker/project-offloads/codex-pc-prov-p1o-20261110/NHR_target/x86_64-unknown-linux-gnu/release/.fingerprint'
d['pinned_setting']='cargo --jobs 1; effective RUSTFLAGS = stager -Zthreads=1 -C link-arg=-Wl,--threads=1 then -C overflow-checks=yes (no extra -Zthreads)'
json.dump(d,open(f,'w'),indent=1)
PY
