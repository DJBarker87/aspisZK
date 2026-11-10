#!/bin/bash
# usage: bash PCQJ_mkspec2.sh RUN TOOL(original|extended) NAMESPACE ROOTS(comma) OPAQUE(comma,may be empty) FEATURES
cd "$(dirname "$0")"
python3 -B - "$@" <<'PY'
import json,sys
run,tool,ns,roots,opq,feat=sys.argv[1:7]
import os
MAN=os.environ.get('MANIFEST','crates/aspis-r1-cost-probe/Cargo.toml');CLIENT=os.environ.get('CLIENT_FEAT','prover,r1p-check,private-leaf-salts')
stable=HOST_STABLE='/home/dombarker/project-offloads/codex-pc-prov-p1m-20261110/PCQJ_stable/'+(sys.argv[7] if len(sys.argv)>7 else 'repro')+'.llbc'
roots=[x for x in roots.split(',') if x];opq=[x for x in opq.split(',') if x]
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1m-20261110'
TOOLS={'extended':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','original':'/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'}
c=['/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for r in roots:c+=['--start-from',r]
for o in opq:c+=['--opaque',o]
c+=['--dest-file',stable,'--','--manifest-path',HOST+'/PCQJ_workspace/'+MAN,'--locked','--offline','--release','--lib','--jobs','1','--features',feat]
a=[TOOLS[tool],'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',HOST+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',HOST+'/'+run+'_emitted/repro.llbc']
d=dict(run=run,spec_id=run,charon_command=c,aeneas_command=a,aeneas_tool=tool,
 opacity=[dict(path=o,why='PCQJ_ changed shape: opaque callee, see PCQJ_CLASSIFICATIONS.json') for o in opq],
 configuration=dict(roots=roots,namespace=[ns],features=[feat],opaque=opq,manifest=MAN),
 features_override=CLIENT,llbc_stable=stable,
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 extra_env={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'},
 configuration_overflow_checks='ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true; -C overflow-checks=yes appended to the stager RUSTFLAGS)',
 frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_source_tree_git_hash='d461fbc56cec8ba29678d6613fc38e6c795d6a66')
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,tool,ns,roots,opq)
PY
