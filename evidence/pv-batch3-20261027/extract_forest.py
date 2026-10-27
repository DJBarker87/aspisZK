from run import H,run
import json,hashlib,sys
P=H/'source/evidence/pv-batch3-20261027/extract'
roots={132:'pool_v1_pair_forest_relation_free_mask_cells_v1',133:'pool_v1_pair_forest_copy_active_rows_v1',134:'pool_v1_pair_forest_copy_active_row_masks_v1',228:'build_pool_v1_pair_forest_copy_registry_v1'}
tools={'/home/dombarker/project-offloads/codex-pv-extract-20261027/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
for p,h in tools.items():assert hashlib.sha256(__import__('pathlib').Path(p).read_bytes()).hexdigest()==h
op=int(sys.argv[1]);suffix=sys.argv[2];llbc=H/f'PV_B3_Forest_{op}_{suffix}.llbc';env={'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','RUSTFLAGS':'--cfg pv_cb_extract','CARGO_TARGET_DIR':str(H/'charon-target')}
cmd=['timeout','180','taskset','--cpu-list','0-3',next(iter(tools)),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::host_forest::'+roots[op],'--include','pv_b3_forest_extraction::host_forest::*','--include','aspis_core::field::*','--include','aspis_statement::pool_v1::pair_tree_hiding::*','--include','aspis_statement::pool_v1::pair_tree_profile::*','--include','aspis_statement::pool_v1::pair_forest_hiding::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
status=run(f'charon-{op}-{suffix}',cmd,'optimized MIR compilation; no arithmetic elimination',env)
if status:sys.exit(status)
out=H/f'generated-{op}-{suffix}';out.mkdir()
cmd=['timeout','180',list(tools)[1],'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_B3_Forest_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)]
sys.exit(run(f'aeneas-{op}-{suffix}',cmd,'symbolic extraction with unchanged preflight and strict joins'))
