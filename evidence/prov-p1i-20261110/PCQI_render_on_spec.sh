#!/bin/bash
# usage: bash PCQI_render_on_spec.sh NMH_E003 PCQI_E001 [extended|original]
# Clone an archived OFF emission spec (emission-repro-20261110/<src>_spec.json) into an overflow-checks-ON spec for this job.
# Changes ONLY: run name, host base paths (workspace, dest), aeneas binary (tool selector), extra_env (ON), cgroup limits.
cd "$(dirname "$0")"
python3 -B - "$1" "$2" "${3:-extended}" <<'PY'
import json,sys,subprocess
src,run,tool=sys.argv[1:4]
d=json.load(open(f'../emission-repro-20261110/{src}_spec.json'))
OLD='/home/dombarker/project-offloads/codex-cx-emission-repro-20261110'
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1i-20261110'
def fix(c):
    return [x.replace(OLD+'/NMH_workspace',HOST+'/PCQI_workspace').replace(OLD+'/'+src+'_emitted',HOST+'/'+run+'_emitted') for x in c]
d['charon_command']=fix(d['charon_command']);d['aeneas_command']=fix(d['aeneas_command'])
assert not any('emission-repro' in x for x in d['charon_command']+d['aeneas_command'])
TOOLS={'extended':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','original':'/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'}
d['aeneas_command'][0]=TOOLS[tool];d['aeneas_tool']=tool
d['derived_from']=src+'_spec.json (archived OFF emission spec)'
d['run']=run
d['spec_id']=src
d['expected_limits']={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
d['extra_env']={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'}
d['configuration_overflow_checks']='ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true; -C overflow-checks=yes appended to the stager RUSTFLAGS)'
d['configuration'].setdefault('namespace',d['aeneas_command'][d['aeneas_command'].index('-namespace')+1])
d['frozen_revision']='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',d['frozen_revision']+'^{tree}'],text=True).strip()
json.dump(d,open(run+'_spec.json','w'),indent=1)
print(run+'_spec.json',d['aeneas_command'][0].split('/')[-1],d['configuration']['namespace'])
PY
