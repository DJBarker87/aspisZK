#!/bin/bash
# Build PRVEq_O1clean.lean: the 10 theorems PCUI_ credited from PRVEq_bundle_O1 (scope PCUI_L029, exit 1), alone.
cd "$(dirname "$0")"
python3 -B - <<'PY'
import re,json
P='../prov-p2i-20261110/'
credited=json.load(open(P+'PCUI_PROVED_OTHER.json'))
want={v['theorem'] for v in credited.values()}
assert len(want)==10
srcs=['PRVEq_AspisR1RecordParser_Funs_o1','PRVEq_NID_ResumeEmissionTypes_o2','PRVEq_NJC_ValidateEmission_o1']
imports=['import Aeneas'];body=[];found=set()
for s in srcs:
    t=open(P+s+'.lean').read().split('\n')
    pre=[];i=0
    # header: comments, imports, then everything up to first 'set_option maxHeartbeats 200000 in' that precedes a PRVEq decl
    chunks=[];cur=[];first_eq=None
    for idx,l in enumerate(t):
        if l.startswith('import '):
            if l not in imports: imports.append(l)
    # split off equality section
    k=next(i for i,l in enumerate(t) if l.startswith('end ') and 'PRVFresh' not in l and i>12)
    head=[l for l in t[:k+1] if not l.startswith('import ')]
    eq=t[k+1:]
    body+=head
    # chunks: 'set_option maxHeartbeats 200000 in' ... '#print axioms X'
    i=0
    while i<len(eq):
        if eq[i].startswith('set_option maxHeartbeats 200000 in'):
            j=i
            while not eq[j].startswith('#print axioms'): j+=1
            ch=eq[i:j+1]
            m=re.match(r'(theorem|def) (\S+)',ch[1])
            name=m.group(2)
            if m.group(1)=='theorem' and (name in want or 'RecordParser' in name):
                body+=ch+['']; found.add(name)
            i=j+1
        else: i+=1
assert want<=found,(want-found)
open('PRVEq_O1clean.lean','w').write('\n'.join(imports)+'\n'+'\n'.join(body)+'\n')
print(len(found),'theorems')
PY
grep -c sorry PRVEq_O1clean.lean; grep -n '^import\|^namespace\|^end ' PRVEq_O1clean.lean
