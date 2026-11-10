#!/bin/bash
# usage: bash PCUJ_render_p_spec.sh <src spec relative to evidence/> <src host base> <src run> <new run>
# Clone an ON P1 spec and add `--include aspis_core::field::P` (transparent field P const) -- shape change for the EXTERNAL_P_NO_TRANSPARENT_EMISSION records.
cd "$(dirname "$0")"
python3 -B - "$@" <<'PY'
import json,sys,subprocess
src,oldhost,oldrun,run=sys.argv[1:5]
d=json.load(open('../'+src))
HOST='/home/dombarker/project-offloads/codex-pc-prov-p2j-20261110'
def fix(c):
    out=[]
    for x in c:
        x=x.replace(oldhost+'/'+oldrun+'_emitted',HOST+'/'+run+'_emitted')
        import re
        x=re.sub(re.escape(oldhost)+r'/PCQ[A-Z]?_workspace',HOST+'/PCUJ_workspace',x)
        out.append(x)
    return out
ch=fix(d['charon_command']);ae=fix(d['aeneas_command'])
assert not any(oldhost in x for x in ch+ae),[x for x in ch+ae if oldhost in x]
assert 'aspis_core::field::P' not in ch
k=ch.index('--dest-file');ch=ch[:k]+['--include','aspis_core::field::P']+ch[k:]
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended'
tool='extended' if ae[0]==TOOL else 'original'
assert ae[0]==TOOL or ae[0].endswith('PCWC_T001_out/work/bin/aeneas'),ae[0]
d.update(run=run,charon_command=ch,aeneas_command=ae,aeneas_tool=tool,spec_id=d.get('spec_id','')+'+P')
d['configuration']['include']=list(d['configuration'].get('include',[]))+['aspis_core::field::P']
d['derived_from']=src+' plus --include aspis_core::field::P (shape change: transparent P)'
d['expected_limits']={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
assert d['extra_env']['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';d['frozen_revision']=rev
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',rev+'^{tree}'],text=True).strip()
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run+'_spec.json',d['configuration']['namespace'])
PY
