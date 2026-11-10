#!/usr/bin/env python3
"""PCVC driver: PRVEq_<M>_P3.lean for module M from the P2g file + FOR_P3 items (fresh-file order)."""
import json,re,sys
sys.path.insert(0,'.')
import gen_loops,mkbase
SHIMNAMES=[]   # fully qualified shim names to unfold with simp only (PCVD)
P2G='../prov-p2g-20261109/'
items=json.load(open(P2G+'PCUG_FOR_P3.json'))['items']
def fname(mod): return P2G+'PRVEq_'+mod.replace('.','_')+'.lean'
def nonloop(base,name,done,F,G,NSF,consts):
    consts=consts+SHIMNAMES+(['Aeneas.Std.bind_tc_ok','Aeneas.Std.bind_ok'] if SHIMNAMES else [])
    sc=', '.join(done+consts)
    gg=gen_loops.gq(G,name)
    sx=f"simp only [{sc}]; " if sc else ""
    return f'''
set_option maxHeartbeats 100000 in
open {NSF} in
theorem PRVC.Eq.{name} : @{F}{name} = @{gg} := by
  first
  | (delta {F}{name} {gg}; with_reducible rfl)
  | (delta {F}{name} {gg}; {sx}with_reducible rfl)
  | (delta {F}{name} {gg}; {sx}done)
  | (delta {F}{name} {gg}; {sx}rfl)
  | (delta {F}{name} {gg}; rfl)
#print axioms PRVC.Eq.{name}
'''
def nonloop_simp(base,name,done,F,G,NSF,consts):
    consts=consts+SHIMNAMES
    sc=', '.join(done+consts)
    gg=gen_loops.gq(G,name)
    return f'''
set_option maxHeartbeats 1000000 in
open {NSF} in
theorem PRVC.Eq.{name} : @{F}{name} = @{gg} := by
  delta {F}{name} {gg}
  simp only [{sc}]
  all_goals with_reducible rfl
#print axioms PRVC.Eq.{name}
'''
def gen(mod,out,only=None,skip=()):
    src=fname(mod)
    tmp='/tmp/_b_'+re.sub(r'\W','_',mod)+'.lean'
    mkbase.mk(src,tmp)
    base=open(tmp).read()
    ns=re.search(r'namespace (\w+)\nnamespace (PRVFresh_\w+)',base)
    G=ns.group(1)+'.'; F=G+ns.group(2)+'.'; NSF=G+ns.group(2)
    its=[i for i in items if i['module']==mod and i['status']=='FAILED']
    wanted=[i['definition'].split('.',1)[1] for i in its]
    thms=re.findall(r'^theorem PRVEq\.[^ ]*?\.(\S+) :',base,re.M)
    fresh_part=base[base.index('namespace '+ns.group(2)):base.index('end '+ns.group(2))]
    alld=[m.group(1) for m in re.finditer(r'^(?:@\[[^\]]*\][ \n])?def\s+(\S+)',fresh_part,re.M) if not m.group(1).endswith('.body')]
    pos={}
    for w in alld:
        m=re.search(r'\ndef\s+'+re.escape(w)+r'\n',fresh_part) or re.search(r'def\s+'+re.escape(w)+r'\b',fresh_part)
        pos[w]=m.start()
    order=[w for w in sorted(pos,key=pos.get) if (w in wanted or all(not t.endswith(w) for t in thms)) and w not in skip]
    done=re.findall(r'^theorem (PRVEq\.\S+) :',base,re.M)
    txt=base.rstrip()+'\n'
    rep={}
    for w in order:
        if only and w not in only: continue
        t=gen_loops.one(base,w,done,F,G,NSF)
        kind='loop'
        if t is None:
            t=nonloop(base,w,done,F,G,NSF,[]); kind='nonloop'
        txt+=t; done.append('PRVC.Eq.'+w); rep[w]=kind
    missing=[w for w in wanted if w not in pos]
    open(out,'w').write(txt)
    return rep,missing
if __name__=='__main__':
    mod,out=sys.argv[1:3]
    print(gen(mod,out))
