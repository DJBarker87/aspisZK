#!/usr/bin/env python3
"""PCWJ_mkspec.py RUN NAMESPACE CRATE FEATURES ROOTS(comma) [INCLUDES(comma)] [--aeneas-only]
Clone the archived frozen-4bb3b3f cost-probe sampler spec NMH_E021 (roots/namespace/paths/environment changed only):
ON configuration (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true, RUSTFLAGS -C overflow-checks=yes), cargo --jobs 4 + CARGO_BUILD_JOBS=4,
stable --dest-file (RUN_repro.llbc in the host workspace) with RUN_emitted/repro.llbc to be pre-created as a symlink to it,
original Aeneas 959659a6 (PCWC_T001_out of the p4c workspace, sha256 checked by PCWJ_extract.py)."""
import json,sys,subprocess
sys.dont_write_bytecode=True
run,ns,crate,feat,roots=sys.argv[1:6]
inc=[x for x in (sys.argv[6] if len(sys.argv)>6 else '').split(',') if x]
HOST='/home/dombarker/project-offloads/codex-pc-prov-p5a-20261110'
ORIG='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
d=json.load(open('../emission-repro-20261110/NMH_E021_spec.json'))
c=d['charon_command']
head=c[:c.index('--start-from')]
for x in inc: head+=['--include',x]
nc=head
for r in roots.split(','): nc+=['--start-from',r]
nc+=['--dest-file',HOST+'/'+run+'_repro.llbc','--','--manifest-path',HOST+'/PCWJ_workspace/crates/'+crate+'/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features',feat]
ae=[ORIG,'-diagnose-translation','-sequential','-no-progress-bar','-backend','lean','-namespace',ns,'-dest',HOST+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',HOST+'/'+run+'_emitted/repro.llbc']
for k in ('groups','members','bytes','basis','diagnostic_only'): d.pop(k,None)
d.update(run=run,spec_id=run,label='PCWJ '+run,charon_command=nc,aeneas_command=ae,aeneas_tool='original',opacity=[],
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 extra_env={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_BUILD_JOBS':'4'},
 configuration_overflow_checks='ON',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
 pin_note='cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads 1; identity by class receipt PCWE_E003',
 aeneas_sha256='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3')
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',d['frozen_revision']+'^{tree}'],text=True,cwd='/Users/dominic/ZK').strip()
d['configuration']=dict(start_from=roots.split(','),roots=roots.split(','),include=inc,opaque=[],features=feat,manifest='crates/'+crate+'/Cargo.toml',namespace=ns,crate=crate)
json.dump(d,open(run+'_spec.json','w'),indent=1); print(run+'_spec.json',len(nc))
