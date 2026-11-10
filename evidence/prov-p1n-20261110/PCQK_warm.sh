#!/bin/bash
# usage: bash PCQK_warm.sh FROM TO : clone spec FROM to TO with byte-identical Charon args (warm-up rerun of a cold target)
cd "$(dirname "$0")"
python3 -B - "$1" "$2" <<'P'
import json,sys
f,t=sys.argv[1:3]
d=json.load(open(f+'_spec.json'));d['run']=d['spec_id']=t
d['aeneas_command']=[x.replace(f,t) for x in d['aeneas_command']]
json.dump(d,open(t+'_spec.json','w'),indent=1)
P
nohup bash run_extract.sh "$2" >/dev/null 2>&1 &
