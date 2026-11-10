#!/bin/bash
# usage: bash PCWM_mkaen.sh NEWRUN SRCSPEC_RUN original|extended [extra aeneas flags...]  -- Aeneas-only spec on the LLBC saved by SRCSPEC_RUN (original Aeneas 959659a6)
cd "$(dirname "$0")"
python3 -B - "$@" <<'P'
import json,sys
new,src,tool=sys.argv[1:4];extra=sys.argv[4:]
d=json.load(open(src+'_spec.json'));H='/home/dombarker/project-offloads/codex-pc-prov-p5d-20261110'
a=d['aeneas_command'];a=[x.replace(src+'_emitted/raw',new+'_emitted/raw') for x in a]
a[a.index('-no-progress-bar')+1:a.index('-no-progress-bar')+1]=extra
d['aeneas_command']=a;d['aeneas_only']=True
T={'original':('/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas','959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'),'extended':('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958')}
d['aeneas_command'][0]=T[tool][0];d['aeneas_sha256']=T[tool][1];d['aeneas_tool']=tool
d['llbc']=H+'/'+src+'_emitted/repro.llbc';d['llbc_produced_by']=src+' Charon (cargo --jobs 4)'
d['run']=new;d['spec_id']=new;d['derived_from']='PCWM_mkaen.sh from '+src
d['warm_note']='Aeneas only on the saved LLBC; '+src+' Charon passed (63 s) and Aeneas timed out at the 180 s cap'
json.dump(d,open(new+'_spec.json','w'),indent=1);print(new,a)
P
