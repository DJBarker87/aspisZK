from run import H,run
from pathlib import Path
import json,hashlib,sys
P=H/'source/evidence/pv-batch3-20261027/extract-copies'
roots={117:'crate::host_arithmetic::state_only_selected_mask_value',121:'crate::host_arithmetic::evaluate_state_only_polynomial',222:'crate::host_multilinear::multilinear_evaluate_qm31',224:'aspis_prover::host_forest::build_pool_v1_pair_forest_copy_helper_v1',226:'crate::host_public::public_bytes',227:'crate::host_public::terminal_qm31'}
tools={'/home/dombarker/project-offloads/codex-pv-extract-20261027/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
for p,h in tools.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
op=int(sys.argv[1]);suffix=sys.argv[2];llbc=H/f'PV_B3_Copy_{op}_{suffix}.llbc';env={'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','RUSTFLAGS':'--cfg pv_cb_extract','CARGO_TARGET_DIR':str(H/'charon-target')}
cmd=['timeout','180','taskset','--cpu-list','0-3',next(iter(tools)),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from',roots[op],'--include','pv_b3_copies_extraction::*','--include','aspis_prover::host_arithmetic::*','--include','aspis_prover::host_forest::*','--include','aspis_core::field::*','--include','aspis_core::state_only_hiding::STATE_ONLY_HIDING_C1_COLUMNS','--include','aspis_core::state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS','--include','aspis_core::state_only_hiding::STATE_ONLY_HIDING_SUMCHECK_ROUNDS','--include','aspis_core::state_only_hiding::STATE_ONLY_HIDING_FACTOR_DEGREE','--include','aspis_statement::pool_v1::pair_tree_hiding::*','--include','aspis_statement::pool_v1::pair_tree_profile::*','--include','aspis_statement::pool_v1::pair_forest_hiding::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
status=run(f'charon-copy-{op}-{suffix}',cmd,'optimized MIR compilation of the exact copied function; no arithmetic elimination',env)
if status:sys.exit(status)
out=H/f'generated-copy-{op}-{suffix}';out.mkdir();cmd=['timeout','180',list(tools)[1],'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_B3_Copy_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)]
sys.exit(run(f'aeneas-copy-{op}-{suffix}',cmd,'symbolic extraction with unchanged fail-closed preflight and strict joins'))
