#!/bin/bash
# usage: bash PCWL_patch.sh RUN  -- set cargo jobs 4 (CLI + env), original Aeneas without -abort-on-error
cd "$(dirname "$0")"
python3 -B - "$1" <<'P'
import json,sys
run=sys.argv[1];f=run+'_spec.json';d=json.load(open(f));c=d['charon_command']
i=c.index('--jobs');c[i+1]='4'
d.setdefault('extra_env',{})['CARGO_BUILD_JOBS']='4'
a=d['aeneas_command']
a[0]='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas';d['aeneas_tool']='original'
if '-abort-on-error' in a:a.remove('-abort-on-error')
d['jobs_note']='cargo --jobs 4 and CARGO_BUILD_JOBS=4, rustc -Zthreads 1 (not used); identity by class receipt PCWE_E003'
json.dump(d,open(f,'w'),indent=1);print('patched',run)
P
