#!/bin/bash
# usage: bash PCVR_mkspec.sh RUN TOOL(extended|original) NAMESPACE ROOTS(comma) EXTRA_OPAQUE(comma, may be empty) [BASE_SPEC] [DROP_OPAQUE(comma)] [EXTRA_INCLUDE(comma)] [EXTRA_ENV_OFF=1]
# Clone the ON tx2_common spec (PCUJ_E001, extended, 16 opaque) and change only: run name, roots, extra opaque, tool, namespace, host paths.
cd "$(dirname "$0")"
python3 -B - "$@" <<'PY'
import json,sys,copy
run,tool,ns,roots,extra=sys.argv[1:6]
base=sys.argv[6] if len(sys.argv)>6 and sys.argv[6] else '../prov-p2j-20261110/PCUJ_E001_spec.json'
drop=[x for x in (sys.argv[7] if len(sys.argv)>7 else '').split(',') if x]
inc=[x for x in (sys.argv[8] if len(sys.argv)>8 else '').split(',') if x]
off=len(sys.argv)>9 and sys.argv[9]=='1'
d=json.load(open(base))
OLDH='/home/dombarker/project-offloads/codex-pc-prov-p2j-20261110';HOST='/home/dombarker/project-offloads/codex-pc-prov-p1k-20261110'
oldrun=d['run'];oldns=d['aeneas_command'][d['aeneas_command'].index('-namespace')+1]
c=d['charon_command'];c2=[];i=0;seen_sf=False
roots=[x for x in roots.split(',') if x];extra=[x for x in extra.split(',') if x]
while i<len(c):
    if c[i]=='--start-from':
        if not seen_sf:
            seen_sf=True
            for r in roots:c2+=['--start-from',r]
        i+=2;continue
    if c[i]=='--opaque' and (c[i+1] in drop or drop==['ALL']):i+=2;continue
    c2.append(c[i]);i+=1
# insert extra opaque before first --include after the last --opaque
last=(max([j for j,x in enumerate(c2) if x=='--opaque'],default=-2)+1) if any(x=='--opaque' for x in c2) else c2.index('--include')-1
ins=[]
for e in extra:
    if e not in [c2[j+1] for j,x in enumerate(c2) if x=='--opaque']:ins+=['--opaque',e]
c2=c2[:last+1]+ins+c2[last+1:]
for e in inc:
    j=c2.index('--features');c2=c2[:j]+['--include',e]+c2[j:]
import re
def fix(cmd):return [re.sub(r'(PC[A-Z]{2}|PCQ|PCO)_workspace','PCVR_workspace',re.sub(r'codex-pc-prov-[a-z0-9]+-2026[0-9]+',HOST.split('/')[-1],x.replace(oldrun+'_emitted',run+'_emitted'))) for x in cmd]
d['charon_command']=fix(c2);a=fix(d['aeneas_command'])
a[a.index('-namespace')+1]=ns;a[a.index('-subdir')+1]=ns
TOOLS={'extended':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','original':'/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'}
a[0]=TOOLS[tool];d['aeneas_command']=a;d['aeneas_tool']=tool
d['run']=run;d['spec_id']=run;d['derived_from']='PCVR_mkspec.sh from '+base
kept=[] if drop==['ALL'] else [o for o in d.get('opacity',[]) if o.get('selector',o['path']) not in drop and o['path'] not in drop]
for e in extra:
    if not any(o.get('selector',o['path'])==e for o in kept):kept.append(dict(path=e,why='PCVR_ Ops-field boundary: callee modelled as an Ops field in the gate (or library trust)'))
d['opacity']=kept
cf=d['configuration'];cf['roots']=roots;cf['namespace']=[ns];cf['opaque']=[c2[j+1] for j,x in enumerate(c2) if x=='--opaque']
cf.pop('charon_command',None);cf.pop('aeneas_command',None)
if off:
    d.pop('extra_env',None);d['configuration_overflow_checks']='OFF (no extra_env)'
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,tool,ns,len(cf['opaque']),'opaque',roots)
PY
