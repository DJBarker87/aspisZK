#!/usr/bin/env python3
"""PCVA_tokdiff.py FRESH_FUNS GATE_FUNS PREFIX : token-level diff of two Aeneas Funs files (comments removed).
Prints opcodes other than equal; used to classify the difference between a fresh emission and a gate module and to extract the
external-axiom -> NNN_call_k parameter map. Exit 0."""
import sys,re,difflib,json
def toks(p):
    t=open(p).read()
    t=re.sub(r'/-.*?-/','',t,flags=re.S); t=re.sub(r'--[^\n]*','',t)
    return re.findall(r"[A-Za-z_][\w'.]*#?\w*|\d+#?\w*|[^\sA-Za-z_\d]",t)
a=toks(sys.argv[1]);b=toks(sys.argv[2]);pre=sys.argv[3]
sm=difflib.SequenceMatcher(None,a,b,autojunk=False)
mp={};other=[]
for op,i1,i2,j1,j2 in sm.get_opcodes():
    if op=='equal':continue
    A=a[i1:i2];B=b[j1:j2]
    if op=='replace' and len(A)==1 and len(B)==1 and B[0].startswith(pre):
        mp.setdefault(B[0],set()).add(A[0])
    elif op=='insert' and all(x.startswith(pre) for x in B): pass
    else: other.append((op,A[:12],B[:12],i1))
print(json.dumps({k:sorted(v) for k,v in mp.items()},indent=0))
print('OTHER',len(other))
for o in other[:25]: print(o)
