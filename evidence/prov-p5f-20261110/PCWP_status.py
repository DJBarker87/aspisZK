#!/usr/bin/env python3
"""PCWP_status.py: classify the definitions proved fresh = gate in P5f by the external names their fresh closure reaches."""
import re,json,sys
sys.dont_write_bytecode=True
FRESH='PCWP_E002_emitted/raw/PCWP_sop2'
funs=open(FRESH+'/Funs.lean').read(); ext=open(FRESH+'/FunsExternal_Template.lean').read()
pos=[(m.start(),(m.group(1) or m.group(2))) for m in re.finditer(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:partial\s+)?def\s+(\S+)|^(?:@\[[^\n]*\]\s*)*def\s*\n\s+(\S+)',funs)]
blocks={}
for i,(p,n) in enumerate(pos):
    e=pos[i+1][0] if i+1<len(pos) else len(funs); blocks[n]=funs[p:e]
externals=set(re.findall(r'(?m)axiom\s+(\S+)',ext))
ROW={'core.array.from_fn':'HM-D','core.array.Array.map':'HM-D',
 'Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter':'HM-D','core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold':'HM-D',
 'core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold':'HM-F','core.iter.traits.iterator.Iterator.fold.default':'HM-F'}
tok=lambda t:set(re.findall(r"[A-Za-z_][\w.']*",t))
refs={n:(tok(b)-{n}) for n,b in blocks.items()}
def closure(n):
    seen=set();st=[n]
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x)
        for r in refs.get(x,()):
            if r in blocks: st.append(r)
    ex=set()
    for x in seen:
        for r in refs.get(x,()):
            if r in externals: ex.add(r)
    return seen,ex
def classify(n):
    c,ex=closure(n)
    rows={ROW[e] for e in ex if e in ROW}
    names=sorted(e for e in ex if e in ROW)
    boundary=sorted(e for e in ex if e not in ROW)
    return rows,names,boundary,len(c)
if __name__=='__main__':
    out=[]
    for f,mod,pfx in (('PCWP_L011/sources/PCWP_sources/PRVEq_RPu_FIq_Native04_n04c.lean','RPu_FIq_Native04','PRVEq.RPu_FIq_Native04_n04.'),
                      ('PCWP_L017/sources/PCWP_sources/PRVEq_RPu_FIq_Native05_n05_c.lean','RPu_FIq_Native05','PRVEq.RPu_FIq_Native05_n05.'),
                      ('PCWP_L024/sources/PCWP_sources/PRVEq_RPu_FIq_Native07_n07_c.lean','RPu_FIq_Native07','PRVEq.RPu_FIq_Native07_n07.')):
        s=open(f).read()
        for m in re.finditer(r'(?m)^theorem ((?:PRVEq|PRVC\.Eq)\.\S+) : @(\S+) = @(\S+) :=',s):
            th,fr,ga=m.groups()
            short=th[len(pfx):] if th.startswith(pfx) else th[len('PRVC.Eq.'):]
            rows,names,boundary,n=classify(short)
            out.append(dict(module=mod,definition='FIq_Native.'+short,theorem=th,file=f.split('/')[-1],
              cls=('DEPENDS_ON_LIBRARY_TRUST' if rows else 'EQUALITY_PROVED'),rows=sorted(rows),library_externals=names,shared_boundary_externals=boundary,closure_size=n))
    json.dump(out,open('gen/classified_raw.json','w'),indent=1)
    from collections import Counter
    print(Counter((o['module'],o['cls']) for o in out))
