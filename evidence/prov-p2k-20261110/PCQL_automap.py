#!/usr/bin/env python3
"""PCQL_automap.py GATE_SRC FRESH_FUNS OUT.json : deterministic name map fresh->gate by unique dotted-suffix match
(gate declaration name tail equals a suffix of exactly one fresh declaration name, and vice versa). Recorded, never applied to emitted text."""
import re,sys,json
gate=''.join(open(x).read() for x in sys.argv[1].split(','));fresh=''.join(open(x).read() for x in sys.argv[2].split(','))
D=lambda t:re.findall(r'(?m)^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|partial\s+)*(?:def|structure|inductive|abbrev)\s+(\S+)',t)
g=D(gate);f=D(fresh);ns=(re.findall(r'(?m)^namespace\s+(\S+)',gate) or [''])[0]
gl=[x[len(ns)+1:] if x.startswith(ns+'.') else x for x in g]
fs=set(f);m={};amb=[]
for x in gl:
    if x in fs: continue
    c=[y for y in f if y.endswith('.'+x)]
    if len(c)==1: m[c[0]]=x
    elif len(c)>1: amb.append((x,c))
json.dump(m,open(sys.argv[3],'w'),indent=1);print(len(g),len(m),'ambiguous',len(amb),[a[0] for a in amb][:5])
