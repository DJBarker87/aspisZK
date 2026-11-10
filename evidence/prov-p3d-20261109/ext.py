#!/usr/bin/env python3
"""ext.py: extend an existing compiled *_P3.lean (or P2f/P2g PRVEq file with the loop bridge) with
   (a) restored dropped fresh blocks, (b) inserted transparent fresh blocks (callee transport), (c) generated equality theorems."""
import re,sys,json
sys.path.insert(0,'.')
import gen_loops,gen_p3
def build(infile,out,undrop=(),insert=(),steps=(),extra='',insert_before=None,bridge=False):
    txt=open(infile).read()
    if bridge and 'namespace PRVC' not in txt:
        b=open('PRVC_LoopBridge.lean').read().split("open Lean.Order\n",1)[1]
        k="set_option maxRecDepth 2048\n"
        assert k in txt
        txt=txt.replace(k,k+"open Lean.Order\n"+b,1)
    def rep(m):
        t=m.group(1)
        d=re.search(r'(?:^|\n)def\s+(\S+)',t)
        if d and d.group(1) in undrop: return t+'\n\n'
        return m.group(0)
    txt=re.sub(r'/- PRV-FRESH-DROPPED[^\n]*\n(.*?)\n-/\n\n?',rep,txt,flags=re.S)
    ns=re.search(r'namespace (\w+)\nnamespace (PRVFresh_\w+)',txt)
    G=ns.group(1)+'.'; F=G+ns.group(2)+'.'; NSF=G+ns.group(2)
    if insert:
        blk='\n\n'.join(insert)+'\n\n'
        if insert_before:
            i=txt.index(insert_before)
        else:
            m=re.search(r'/- PRV-FRESH-DROPPED|end '+ns.group(2),txt); i=m.start()
        txt=txt[:i]+blk+txt[i:]
    done=re.findall(r'^theorem (PRVEq\.\S+) :',txt,re.M)+re.findall(r'^theorem (PRVC\.Eq\.\S+) :',txt,re.M)
    res=txt.rstrip()+'\n'
    for kind,name,*opt in steps:
        if kind=='loop': t=gen_loops.one(res,name,done,F,G,NSF); assert t,name
        else: t=gen_p3.nonloop(res,name,done,F,G,NSF,[])
        res+=t; done.append('PRVC.Eq.'+name)
    res+=extra
    open(out,'w').write(res)
    return res
