#!/bin/bash
# usage: bash PCWM_fixllbc.sh RUN LLBC_PATH  -- point an Aeneas-only spec at an LLBC outside <run>_emitted
cd "$(dirname "$0")"
python3 -B - "$1" "$2" <<'P'
import json,sys
run,l=sys.argv[1:3];f=run+'_spec.json';d=json.load(open(f))
d['llbc']=l;d['aeneas_command'][-1]=l;d['llbc_produced_by']=d['llbc_produced_by']+' (dest-file '+l+')'
json.dump(d,open(f,'w'),indent=1);print(d['aeneas_command'][-3:])
P
