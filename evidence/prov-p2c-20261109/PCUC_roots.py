#!/usr/bin/env python3
"""PCUC_roots.py: from the round-1 probe logs, find the fresh declarations that fail to elaborate (errors inside a fresh `def`, not inside a PRVEq theorem)
and classify the first error of each: root-cause map gen/roots.json {label: {fresh_decl: {class, first_error}}}."""
import re,json
bund=json.load(open('gen/bundles.json'));roots={}
def cls(msg,ctx):
    t=msg+' '+ctx
    if 'aspis_core.field.P' in t and 'U32' in t: return 'EXTERNAL_CONST_FORM (gate aspis_core.field.P : U32 constant; fresh axiom aspis_core.field.P : Result U32)'
    if re.search(r'Unknown identifier `(aspis_core\.field\.|MutAArray)',t): return 'NAME_MISMATCH (fresh name absent from the gate module: gate hand-adapted naming/externals)'
    if 'expected' in msg and '=>' in msg: return 'FRESH_PARSE_ERROR (fresh text does not parse under the pinned Lean)'
    return 'OTHER'
for bk,labels in bund.items():
    offs=json.load(open(f'gen/bundle_{bk}1_offsets.json'));bl=open(f'PRVEq_bundle_{bk}1.lean').read().split('\n');log=open(f'gen/{bk}_1.log').read().split('\n')
    ranges={}
    for lab in labels:
        lm=offs['PRVEq_'+lab]['line_map'];ranges[lab]=(lm[0][1],lm[-1][1])
    for i,l in enumerate(log):
        m=re.match(r'.*bundle_\w+\.lean:(\d+):(\d+): error[^:]*: (.*)',l)
        if not m: continue
        ln=int(m.group(1))
        k=ln-1
        while k>0 and not re.match(r'^(def|theorem|structure|abbrev|inductive)\s',bl[k]): k-=1
        head=bl[k]
        if head.startswith('theorem'): continue
        mm=re.match(r'^def\s+(\S+)',head)
        lab=next((lb for lb,(a,b) in ranges.items() if a<=ln<=b),None)
        ctx=' '.join(x.strip() for x in log[i+1:i+4])
        c=cls(m.group(3),ctx)
        roots.setdefault(lab,{}).setdefault(mm.group(1),dict(cls=c,first_error=(m.group(3)+' '+ctx)[:300],bundle_line=ln))
json.dump(roots,open('gen/roots.json','w'),indent=1)
for lab,v in roots.items():
    for n,x in v.items(): print(lab,n,x['cls'][:40])
