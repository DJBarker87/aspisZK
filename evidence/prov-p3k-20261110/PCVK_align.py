#!/usr/bin/env python3
"""PCVK_ alignment helper: for the fresh blocks of a stage, align fresh and gate tokens and list (external -> gate token pattern) pairs, plus all other differences."""
import re,sys,json,difflib
raw,gatepath,fragjson,blocks=sys.argv[1:5]
fj=json.load(open(fragjson));ext=set(fj['fields'].values())
funs=open(raw+'/Funs.lean').read();gate=open(gatepath).read()
def blk(t,name):
    m=re.search(r'\ndef\s+'+re.escape(name)+r'(?=[\s(])',t)
    if not m:return None
    s=m.start();e=t.find('\n/--',s+1);return t[s:e if e>0 else None]
tok=lambda s:re.findall(r"[\w.'#«»]+|[^\s\w]",s)
for name in blocks.split(','):
    f=blk(funs,name);g=blk(gate,name)
    if f is None or g is None:print('MISSING',name,f is None,g is None);continue
    tf,tg=tok(f),tok(g)
    sm=difflib.SequenceMatcher(None,tf,tg,autojunk=False)
    print('==',name,len(tf),len(tg))
    for op,i1,i2,j1,j2 in sm.get_opcodes():
        if op=='equal':continue
        print(' ',op,' '.join(tf[i1:i2])[:140],'  ==>  ',' '.join(tg[j1:j2])[:140])
