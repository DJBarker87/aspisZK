#!/usr/bin/env python3
"""New-selection / changed-shape spec for P1c. Starts from an already rendered PCQC_ spec (template), replaces run id,
spec id, label, start_from roots, opaque selectors, namespace, covers, and records why.
Usage: python3 PCQC_make_variant.py TEMPLATE_SPEC NEW_RUN SPEC_ID NAMESPACE START_FROM(comma) OPAQUE(comma or -) KIND NOTE [COVERS_JSON]"""
import json,sys
from pathlib import Path
E=Path(__file__).resolve().parent
tpl,new,sid,ns,sf,op,kind,note=sys.argv[1:9]
covers=json.loads(sys.argv[9]) if len(sys.argv)>9 else None
s=json.loads(Path(tpl).read_text());old=s['run']
t=json.dumps(s).replace(old,new)
s=json.loads(t)
def strip(cmd,flag):
    out=[];i=0
    while i<len(cmd):
        if cmd[i]==flag:i+=2;continue
        out.append(cmd[i]);i+=1
    return out
ch=strip(strip(s['charon_command'],'--start-from'),'--opaque')
i=ch.index('--dest-file')
add=[]
for r in sf.split(','):add+=['--start-from',r]
if op!='-':
    for o in op.split(','):add+=['--opaque',o]
ch=ch[:i]+add+ch[i:]
s['charon_command']=ch
old_ns=s['configuration']['namespace']
ae=s['aeneas_command'];ae=[ns if x==old_ns else x for x in ae];s['aeneas_command']=ae
s['spec_id']=sid;s['label']=sid
c=s['configuration'];c['start_from']=sf.split(',');c['opaque']=[] if op=='-' else op.split(',');c['namespace']=ns
if covers:s['covers']=covers
s['extra_env']={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'}
s['p1c']=dict(kind=kind,earlier_run=None,template_spec=Path(tpl).name,note=note)
(E/(new+'_spec.json')).write_text(json.dumps(s,indent=1)+'\n');print(new,sid,ns)
