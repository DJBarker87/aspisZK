#!/bin/bash
# usage: bash PCQI_mkspec.sh RUN NAMESPACE MANIFEST_CRATE FEATURES TOOL(extended|original) LABEL START1 [START2 ...]
# builds an overflow-checks-ON spec from the PCQF_E007 template (same stager/controller shape); opaque/include via env OPAQUE / INCLUDE (space separated)
cd "$(dirname "$0")"
RUN=$1; NS=$2; CRATE=$3; FEAT=$4; TOOL=$5; LABEL=$6; shift 6
RUN=$RUN NS=$NS CRATE=$CRATE FEAT=$FEAT TOOL=$TOOL LABEL=$LABEL STARTS="$*" python3 -B - <<'PY'
import json,os,subprocess
e=os.environ;run=e['RUN'];ns=e['NS']
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1i-20261110'
d=json.load(open('../prov-p1e-20261109/PCQF_E007_spec.json'))
starts=e['STARTS'].split();opaque=e.get('OPAQUE','').split();inc=e.get('INCLUDE','').split()
ch=['/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for s in starts: ch+=['--start-from',s]
for o in opaque: ch+=['--opaque',o]
for i in inc: ch+=['--include',i]
ch+=['--dest-file',f'{HOST}/{run}_emitted/repro.llbc','--','--manifest-path',f"{HOST}/PCQI_workspace/crates/{e['CRATE']}/Cargo.toml",'--locked','--offline','--release','--lib','--jobs','1','--features',e['FEAT']]
TOOLS={'extended':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','original':'/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'}
ae=[TOOLS[e['TOOL']],'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',f'{HOST}/{run}_emitted/raw','-subdir',ns,'-split-files',f'{HOST}/{run}_emitted/repro.llbc']
d.update(run=run,spec_id=run,label=e['LABEL'],charon_command=ch,aeneas_command=ae,aeneas_tool=e['TOOL'],opacity=[])
d['configuration']=dict(start_from=starts,include=inc,opaque=opaque,features=e['FEAT'],manifest=f"crates/{e['CRATE']}/Cargo.toml",namespace=ns,crate=e['CRATE'])
d.pop('p1e',None);d.pop('covers',None);d['derived_from']='prov-p1e-20261109/PCQF_E007_spec.json (shape template)'
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',d['frozen_revision']+'^{tree}'],text=True).strip()
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run+'_spec.json')
PY
