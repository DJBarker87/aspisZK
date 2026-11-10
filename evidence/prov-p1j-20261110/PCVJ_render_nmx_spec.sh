#!/bin/bash
# Overflow-ON spec for the NMX_registry emission (tx2-auth-20261111/NMX_registry_emitted): the archived NMX_PINS charon/aeneas argument
# arrays with only the host paths (workspace, dest) relocated. Stager controller: PCVJ_extract.py (NHR_stage, opacity=[] as PCQD_E027).
cd "$(dirname "$0")"
python3 -B - "$1" <<'PY'
import json,sys,subprocess
run=sys.argv[1]
pins=json.load(open('../tx2-auth-20261111/NMX_registry_emitted/NMX_PINS.json'))
OLD='/home/dombarker/project-offloads/codex-cx-tx2-auth-20261111'
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1j-20261110'
def fix(c):
    return [x.replace(OLD+'/NMX_src',HOST+'/PCVJ_workspace').replace(OLD+'/NMX_registry_emitted/registry.llbc',HOST+'/'+run+'_emitted/repro.llbc').replace(OLD+'/NMX_registry_emitted',HOST+'/'+run+'_emitted') for x in c]
ch=fix(pins['charon_command']);ae=fix(pins['aeneas_command'])
assert not any('tx2-auth' in x for x in ch+ae),(ch,ae)
ae[0]='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
d=dict(run=run,spec_id='NMX_registry',aeneas_tool='extended',charon_command=ch,aeneas_command=ae,opacity=[],
 configuration=dict(start_from=['crate::r1_pool_adapter::owned::authenticate_invariant_release_registry'],include=[],opaque=['crate::r1_pool_adapter::owned::require_readonly_account','solana_account_info::AccountInfo'],
   features='pool-adapter,private-leaf-salts',manifest='programs/r1-cost-probe/Cargo.toml',namespace='NMX_registry',crate='aspis-r1-cost-probe-program'),
 derived_from='tx2-auth-20261111/NMX_registry_emitted/NMX_PINS.json (archived OFF emission; aeneas there ran without -abort-on-error and exited 1)',
 frozen_revision=rev,frozen_source_tree_git_hash=subprocess.check_output(['git','rev-parse',rev+'^{tree}'],text=True).strip(),
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 extra_env={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'},
 configuration_overflow_checks='ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true; -C overflow-checks=yes appended to the stager RUSTFLAGS)')
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run+'_spec.json')
PY
