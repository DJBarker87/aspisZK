from pathlib import Path
import json,subprocess,shutil,runpy,sys
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027')
# Reuse the measurement function without executing the probe loop.
s=(D/'run_host.py').read_text().split('roots=')[0];exec(s)
jobs={79:('aspis_core::r0::encoder::eval_message','aspis_core::r0::encoder::*'),117:('aspis_core::state_only_hiding::state_only_selected_mask_value','aspis_core::state_only_hiding::*'),121:('aspis_core::state_only_sumcheck::evaluate_state_only_polynomial','aspis_core::state_only_sumcheck::*'),222:('aspis_statement::constraints_v4::multilinear_evaluate_qm31','aspis_statement::constraints_v4::*'),251:('aspis_r1_cost_probe::weights::Weights::materialize','aspis_r1_cost_probe::weights::*'),252:('aspis_r1_cost_probe::weights::Weights::new','aspis_r1_cost_probe::weights::*'),253:('aspis_r1_cost_probe::weights::Weights::raw','aspis_r1_cost_probe::weights::*')}
for op in map(int,sys.argv[1:]):
 # Each variant changes only the task-private source snapshot; restore previous variant first.
 for path in (D/'source-inputs').glob('*/*/aspis-*/src/**/*.rs'):
  rel=path.relative_to(D/'source-inputs'/path.relative_to(D/'source-inputs').parts[0]);orig=BASE/'source'/rel
  if orig.exists():shutil.copyfile(orig,D/'source'/rel)
 for path in (D/'source-inputs'/str(op)).rglob('*.rs'):shutil.copyfile(path,D/'source'/path.relative_to(D/'source-inputs'/str(op)))
 root,inc=jobs[op];crate=root.split('::')[0].replace('_','-');llbc=D/f'PV_R2_{op}.llbc'
 cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D/'source-target'),str(BASE/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',root,'--include',inc,'--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(D/'source'/'Cargo.toml'),'-p',crate,'--features','r0,ct-host-prover' if crate=='aspis-core' else ('r0,pool-v1-kernel' if crate=='aspis-statement' else 'ct-host-prover'),'--release','--offline','--lib','--jobs','4']
 if run(f'charon-{op}-01',cmd,D/'source'):continue
 out=D/f'generated-{op}';out.mkdir();run(f'aeneas-{op}-01',['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)])
