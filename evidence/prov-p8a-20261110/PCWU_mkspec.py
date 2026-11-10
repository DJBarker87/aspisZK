#!/usr/bin/env python3
"""usage: [PCWU_BASE=<base spec>] python3 PCWU_mkspec.py RUN TOOL NAMESPACE ROOTS(comma) [OPAQUE(comma)] [AENEAS_EXTRA_FLAGS(comma)]
TOOL: original | TV3 | TVn (a PCWU tool version listed in PCWU_TOOLS.json with host_bin + sha256).
Clones ../prov-p4y-20261110/PCWO_E002_spec.json (crate aspis-r1-cost-probe, features private-leaf-salts,program-build,
overflow checks ON, cargo --jobs 4, CARGO_BUILD_JOBS=4, codegen units 2) and changes only run, tools, roots, opaque list,
dest-file, namespace and optional extra Aeneas flags (e.g. -log-debug for analysis runs)."""
import json,sys
sys.dont_write_bytecode=True
run,tool,ns,roots=sys.argv[1:5]
opq=[x for x in (sys.argv[5] if len(sys.argv)>5 else '').split(',') if x]
xfl=[x for x in (sys.argv[6] if len(sys.argv)>6 else '').split(',') if x]
H='/home/dombarker/project-offloads/codex-pc-prov-p8a-20261110'
import os
BASE=os.environ.get('PCWU_BASE','../prov-p4y-20261110/PCWO_E002_spec.json')
d=json.load(open(BASE))
T=json.load(open('PCWU_TOOLS.json'))['versions'][tool]
c=d['charon_command'];c2=[];i=0
while i<len(c):
    if c[i] in('--start-from','--opaque'):i+=2;continue
    if c[i]=='--dest-file':
        for r in roots.split(','):c2+=['--start-from',r]
        for o in opq:c2+=['--opaque',o]
        c2+=['--dest-file',H+'/'+run+'_emitted/repro.llbc'];i+=2;continue
    c2.append(c[i]);i+=1
import re
c2=[re.sub(r'/codex-pc-prov-[a-z0-9]+-2026[0-9]+/PC[A-Z]{2}_workspace/','/codex-pc-prov-p8a-20261110/PCWU_workspace/',x) for x in c2]
c2[0]=T['charon']
a=d['aeneas_command'][:];a[0]=T['aeneas']
a[a.index('-namespace')+1]=ns;a[a.index('-subdir')+1]=ns
a[a.index('-dest')+1]=H+'/'+run+'_emitted/raw';a[-1]=H+'/'+run+'_emitted/repro.llbc'
a=a[:-1]+xfl+a[-1:]
d.update(run=run,spec_id=run,charon_command=c2,aeneas_command=a,aeneas_tool=('original' if tool=='original' else tool),aeneas_sha256=T['aeneas_sha256'],
 charon_sha256=T['charon_sha256'],charon_driver_sha256=T.get('charon_driver_sha256'),tool_label=T['label'],tool_version=tool,derived_from=BASE)
d['configuration'].update(roots=roots.split(','),namespace=[ns],opaque=opq)
d['opacity']=[]
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,tool,roots,opq,xfl)
