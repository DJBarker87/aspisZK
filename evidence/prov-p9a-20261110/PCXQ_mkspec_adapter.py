#!/usr/bin/env python3
"""PCXQ: adapter-side specs at 271869c946d with the ORIGINAL tools (Charon daad69be XRa_bin + Aeneas 959659a6 p4c rebuild), command shape copied from NMW_process_emitted (4bb3b3f)
usage: python3 PCXQ_mkspec_adapter.py RUN NAMESPACE ROOTS(comma) OPAQUE(comma)"""
import json,sys
sys.dont_write_bytecode=True
run,ns,roots,opq=sys.argv[1:5]
H='/home/dombarker/project-offloads/codex-pc-prov-p9a-20261110'
XR='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon'
AE='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
import os
SECOND=os.environ.get('PCXQ_TOOL')=='second'
TB='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin'
roots=roots.split(',');opq=[x for x in opq.split(',') if x]
c=[XR,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for r in roots:c+=['--start-from',r]
for o in opq:c+=['--opaque',o]
if SECOND:c[0]=TB+'/charon'
c+=['--dest-file',H+'/'+run+'_emitted/repro.llbc','--','--manifest-path',H+'/PCXQ_workspace/programs/r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features','pool-adapter,private-leaf-salts']
a=[AE,'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',H+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',H+'/'+run+'_emitted/repro.llbc']
if SECOND:
    a[0]=TB+'/aeneas';a.remove('-abort-on-error')
d=dict(run=run,spec_id=run,label='PIN2 adapter at 271869c946d',charon_command=c,aeneas_command=a,opacity=[],aeneas_tool='second' if SECOND else 'original',
 configuration=dict(start_from=roots,include=[],opaque=opq,features='pool-adapter,private-leaf-salts',namespace=[ns],crate='aspis-r1-cost-probe'),
 frozen_revision='271869c946d4286db6ee5be784f136599fa8707e',frozen_source_tree_git_hash='ab33a923c2b50acdefe256308ec8aee8018b0be4',
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 extra_env=({'CARGO_BUILD_JOBS':'4','CARGO_PROFILE_RELEASE_CODEGEN_UNITS':'2','CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_CODEGEN_UNITS':'2'} if SECOND else {'CARGO_BUILD_JOBS':'4'}),aeneas_sha256=('230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91' if SECOND else None),jobs_note='cargo --jobs 4 and CARGO_BUILD_JOBS=4, rustc -Zthreads 1 (stager RUSTFLAGS); identity by class receipt PCWE_E003; release default overflow checks as NMW_process_emitted (no arithmetic in these bodies)')
json.dump(d,open(run+'_spec.json','w'),indent=1)
