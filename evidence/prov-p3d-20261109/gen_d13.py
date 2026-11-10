#!/usr/bin/env python3
"""PCVD item 1, Native13: sliced fresh section.  The fresh 200-line literal constants.COPY_PATTERNS is NOT elaborated
(L034/L042/L043 retired the full section); it enters as an explicit leading parameter instantiated with the gate constant."""
import re,sys
sys.path.insert(0,'.')
import mkbase,gen_loops,gen_p3
mod='RPu_FIq_Native13'; out=sys.argv[1]
src=gen_p3.fname(mod); s=open(src).read()
s=re.sub(r'/- PRV-OBLIGATION.*?-/\n\n?','',s,flags=re.S)
head,rest=s.split('namespace PRVFresh_RPu_FIq_Native13\n',1)
fresh=rest.split('end PRVFresh_RPu_FIq_Native13',1)[0]
blocks=re.split(r'\n\n(?=/--)',fresh.strip('\n'))
def name(b):
    m=re.search(r'\ndef\s+(\S+)',b); return m.group(1) if m else None
P='pool_v1.pair_forest_copy_terminal.'
want=[P+'lift_m31',P+'pattern_values_literal_loop0.body',P+'pattern_values_literal_loop0',
      P+'pattern_values_literal_loop1_loop0.body',P+'pattern_values_literal_loop1_loop0',
      P+'pattern_values_literal_loop1.body',P+'pattern_values_literal_loop1',P+'pattern_values_literal',P+'pattern_values',
      P+'selector_mask_sum_16_loop.body',P+'selector_mask_sum_16_loop',P+'selector_mask_sum_16',P+'constants.ACTIVE_ROW_MASKS',
      P+'Selectors.active_literal_loop.body',P+'Selectors.active_literal_loop',P+'Selectors.active_literal',P+'Selectors.active']
keep={}
for b in blocks:
    n=name(b)
    if n in want: keep[n]=b
    if 'POSEIDON2_WIDTH' in b and 'def poseidon2.POSEIDON2_WIDTH' in b: keep['poseidon2.POSEIDON2_WIDTH']=b
    if 'POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1\n' in b and 'POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 :' not in b and b.count('def')>=1 and 'PATTERNS_V1]' in b: keep['PATTERNS_V1']=b
assert set(want)<=set(keep),set(want)-set(keep)
CP='(COPY_PATTERNS : Array pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern 14#usize)'
def addparam(b,defname):
    # add COPY_PATTERNS as the first parameter of `def defname`
    return re.sub(r'(\ndef '+re.escape(defname)+r'\n)',r'\1  '+CP+'\n',b,count=1)
KC=P+'constants.COPY_PATTERNS'
b=keep[P+'pattern_values_literal_loop1.body']; b=addparam(b,P+'pattern_values_literal_loop1.body'); b=b.replace(KC,'COPY_PATTERNS'); keep[P+'pattern_values_literal_loop1.body']=b
b=keep[P+'pattern_values_literal_loop1']; b=addparam(b,P+'pattern_values_literal_loop1')
b=b.replace('pattern_values_literal_loop1.body q','pattern_values_literal_loop1.body COPY_PATTERNS q'); keep[P+'pattern_values_literal_loop1']=b
b=keep[P+'pattern_values_literal']; b=addparam(b,P+'pattern_values_literal')
b=b.replace('pattern_values_literal_loop1 q openings','pattern_values_literal_loop1 COPY_PATTERNS q openings'); keep[P+'pattern_values_literal']=b
b=keep[P+'pattern_values']; b=addparam(b,P+'pattern_values'); b=b.replace('pattern_values_literal openings lambda','pattern_values_literal COPY_PATTERNS openings lambda'); keep[P+'pattern_values']=b
shim="/-- PCVD constant binding: cross-crate fresh emission types the constant as `Result`; interpretation `ok <gate constant>`. -/\ndef field.QM31.ZERO : Result field.QM31 := ok FIq_Native.field.QM31.ZERO\n\n/-- PCVD constant binding (see above) -/\ndef field.QM31.ONE : Result field.QM31 := ok FIq_Native.field.QM31.ONE"
order=[k for k in keep if k not in ('poseidon2.POSEIDON2_WIDTH','PATTERNS_V1')]
body='\n\n'.join(([keep['poseidon2.POSEIDON2_WIDTH']] if 'poseidon2.POSEIDON2_WIDTH' in keep else [])+[keep[k] for k in order])
txt=head+'namespace PRVFresh_RPu_FIq_Native13\n\n'+shim+'\n\n'+body+'\n\nend PRVFresh_RPu_FIq_Native13\nend FIq_Native\n'
open('/tmp/_n13slice.lean','w').write(txt)
# inline bridge
bridge=open('PRVC_LoopBridge.lean').read().split("open Lean.Order\n",1)[1]
k="set_option maxRecDepth 2048\n"
txt=txt.replace(k,k+"open Lean.Order\n"+bridge,1)
open('/tmp/_n13base.lean','w').write(txt)
ns='FIq_Native.PRVFresh_RPu_FIq_Native13.'
F=ns; G='FIq_Native.'; NSF='FIq_Native.PRVFresh_RPu_FIq_Native13'
KCg='FIq_Native.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS'
QZ='FIq_Native.field.QM31.ZERO'
gen_loops.HOIST[P+'pattern_values_literal_loop1']={'COPY_PATTERNS':KCg,'q':QZ}
gen_p3.SHIMNAMES[:]=[ns+'field.QM31.ZERO',ns+'field.QM31.ONE']
done=[]
res=txt.rstrip()+'\n'
# nonloop with hoisted C: written directly
def nl(name,hoist):
    sc=', '.join(done+gen_p3.SHIMNAMES+['Aeneas.Std.bind_tc_ok','Aeneas.Std.bind_ok'])
    fa=F+name+''.join(' ('+h+')' for h in hoist)
    return f'''
set_option maxHeartbeats 100000 in
open {NSF} in
theorem PRVC.Eq.{name} : @{fa} = @{G}{name} := by
  first
  | (delta {F}{name} {G}{name}; with_reducible rfl)
  | (delta {F}{name} {G}{name}; simp only [{sc}]; with_reducible rfl)
  | (delta {F}{name} {G}{name}; simp only [{sc}]; done)
  | (delta {F}{name} {G}{name}; rfl)
#print axioms PRVC.Eq.{name}
'''
def nlc(name):   # constants / no hoist
    return nl(name,[])
steps=[('nl','poseidon2.POSEIDON2_WIDTH'),('nl',P+'lift_m31'),('loop',P+'pattern_values_literal_loop0'),('loop',P+'pattern_values_literal_loop1_loop0'),('loop',P+'pattern_values_literal_loop1'),('nlh',P+'pattern_values_literal'),('nlh2',P+'pattern_values'),
       ('nl',P+'constants.ACTIVE_ROW_MASKS'),('loop',P+'selector_mask_sum_16_loop'),('nl',P+'selector_mask_sum_16'),('loop',P+'Selectors.active_literal_loop'),('nl',P+'Selectors.active_literal'),('nl',P+'Selectors.active')]
for kind,w in steps:
    if kind=='nl' and w=='poseidon2.POSEIDON2_WIDTH' and w not in keep: continue
    if kind=='loop': t=gen_loops.one(txt,w,done,F,G,NSF); assert t,w
    elif kind=='nl': t=nlc(w)
    elif kind=='nlh': t=nl(w,[KCg])
    else: t=nl(w,[KCg])
    res+=t; done.append('PRVC.Eq.'+w)
open(out,'w').write(res)
print('ok',len(res))
