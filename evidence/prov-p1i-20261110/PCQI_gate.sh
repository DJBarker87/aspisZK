#!/bin/bash
# usage: bash PCQI_gate.sh MODULE  -> writes inputs/gate_<MODULE>.lean from the first PRV_PARTITION candidate path (git research) and prints the path
cd "$(dirname "$0")"
python3 -B - "$1" <<'PY'
import json,sys,subprocess,os
m=sys.argv[1];p=json.load(open('../prov-plan-20261108/PRV_PARTITION.json'))['modules'][m]
paths=[c['path'] for c in p['candidates']]
for q in paths:
    r=subprocess.run(['git','-C','/Users/dominic/ZK','show','research:'+q],capture_output=True,text=True)
    if r.returncode==0:
        open('inputs/gate_'+m.replace('.','_')+'.lean','w').write(r.stdout);print(q);break
else: print('NOGATE',paths)
PY
