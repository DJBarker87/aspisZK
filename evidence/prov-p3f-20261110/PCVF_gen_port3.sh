#!/bin/bash
# Generates PRVEq_Port3_closures_k2.lean from the OFF emission PCVF_E005 (closure class of Port3_NativeGeometryBody).
python3 -I - <<'PY'
import re,glob
F=glob.glob('PCVF_E005_emitted/raw/*/Funs.lean')[0]
t=open(F).read()
i=t.index('/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<')
j=t.index('end ',i) if 'end ' in t[i:] else len(t)
body=t[i:j]
# split into blocks at doc comments
blocks=re.split(r'(?m)^(?=/--)',body)
blocks=[b for b in blocks if b.strip()]
names=[]
out=[]
EXT={'core.array.from_fn':'x.from_fn','aspis_core.field.M31.ZERO':'x.zero','aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq':'x.eq'}
def defname(b):
    m=re.search(r'(?ms)^(?:@\[[^\]]*\]\s*)?def\s+(\S+)',b)
    return m.group(1)
for b in blocks:
    n=defname(b); names.append(n)
cut=next(i for i,n in enumerate(names) if 'closure' not in n)
blocks=blocks[:cut]; names=names[:cut]
for k,v in EXT.items():
    pass
need=set()
for b,n in zip(blocks,names):
    if any(re.search(re.escape(k)+r'(?![\w.])',b) for k in EXT): need.add(n)
changed=True
while changed:
    changed=False
    for b,n in zip(blocks,names):
        if n in need: continue
        for m in list(need):
            if re.search(re.escape(m)+r'(?![\w])',b.replace(n,'',1)) :
                need.add(n);changed=True;break
res=[]
for b,n in zip(blocks,names):
    for k,v in EXT.items(): b=re.sub(re.escape(k)+r'(?![\w.])',v,b)
    for m in need:
        # references (not the definition head)
        head=re.search(r'(?ms)^(?:@\[[^\]]*\]\s*)?def\s+'+re.escape(n),b)
        pre,post=b[:head.end()],b[head.end():]
        post=re.sub(r'(?<![\w.])'+re.escape(m)+r'(?![\w.])',m+' x',post) if m!=n else post
        b=pre+post
    if n in need:
        head=re.search(r'(?ms)^(?:@\[[^\]]*\]\s*)?def\s+'+re.escape(n),b)
        b=b[:head.end()]+' (x : Ext)'+b[head.end():]
    res.append(b)
open('/tmp/pcvf_port3_names.txt','w').write('\n'.join(('N ' if n in need else 'P ')+n for n in names))
hdr='''-- PCVF_ item 2 (Port3_NativeGeometryBody closure class). Fresh text: OFF emission PCVF_E005 (PCQD E011 spec, no overflow checks,
-- extended Aeneas, frozen 4bb3b3f), closure definitions of QueryGeometry::for_range, external axioms of the emission replaced by Ext.
-- Gate: AspisR1.Port3_NativeGeometryBody (takes ops : Ops CoreError). RESULT CLASS: CONDITIONAL_ON_BINDING for the definitions that use ops
-- (from_fn, M31 zero, M31 eq bound to the emission's externals); closure_4.closure and closure/closure_1/closure_2 need no binding.
import Aeneas
import Port3_NativeGeometryBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1.Port3_NativeGeometryBody
namespace PRVFresh_k2

@@ERRIND@@\n\nstructure Ext where
  from_fn : ∀ {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst : core.ops.function.FnMut F Std.Usize T), F → Result (Array T N)
  zero : Result aspis_core.field.M31
  eq : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool

'''
T=open(glob.glob('PCVF_E005_emitted/raw/*/Types.lean')[0]).read()
m=re.search(r'inductive aspis_core\.r0\.Error where\n(?:\|[^\n]*\n)+',T)
hdr=hdr.replace('@@ERRIND@@',m.group(0).rstrip())
open('/tmp/pcvf_port3_fresh.lean','w').write(hdr+'\n'.join(res)+'\nend PRVFresh_k2\nend AspisR1.Port3_NativeGeometryBody\n')
print(len(names),len(need))
PY
python3 -I - <<'PY'
names=[l.split(' ',1) for l in open('/tmp/pcvf_port3_names.txt').read().split('\n')]
fresh=open('/tmp/pcvf_port3_fresh.lean').read()
G='AspisR1.Port3_NativeGeometryBody.'
F='AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.'
th=['''
namespace PRVEq.Port3_k2
open AspisR1.Port3_NativeGeometryBody
variable {CoreError : Type}

/-- The binding of the gate record fields used by this class to the emission's externals. -/
structure Bound (ops : Ops CoreError) (x : PRVFresh_k2.Ext) : Prop where
  h0 : ∀ {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T) (f : F), ops.op0 N inst f = x.from_fn N inst f
  h5 : ops.op5 = x.eq
  h6 : ops.op6 = x.zero
''']
done=[]
for k,n in names:
    pe=', '.join(f'eq_{i}' for i in range(len(done))) 
    simp='first | rfl | (funext; rfl) | (unfold %s%s %s%s; simp only [%s b.h5, b.h6, b.h0]; rfl) | (funext; unfold %s%s %s%s; simp only [%s b.h5, b.h6, b.h0]; rfl)'
    i=len(done)
    a=(F,n,G,n,(pe+', ') if pe else '')
    isfn = n.endswith('.call_mut') or n.endswith('.call_once')
    rw = ' | '.join([f'rw [eq_{j} b]' for j in range(len(done))]+['rw [b.h6]','rw [b.h5]','simp only [b.h0]'])
    ce = 'PRVFresh_k2.aspis_core.r0.Error' if 'ErrorError' in n else None
    cev = '(CoreError := %s)'%ce if ce else ''
    if k=='N':
        tac = ('funext _ _; ' if isfn else '') + f'unfold {F}{n} {G}{n}; repeat (first | {rw}); try rfl'
        stmt=f'theorem eq_{i} {{ops : Ops {ce or "CoreError"}}} {{x : PRVFresh_k2.Ext}} (b : Bound ops x) :\n    {F}{n} x = {G}{n} ops := by\n  first | rfl | ({tac})'
    else:
        stmt=f'theorem eq_{i} (ops : Ops {ce or "CoreError"}) :\n    {F}{n} = {G}{n} ops := by\n  first | rfl | (funext _ _; rfl) | (unfold {F}{n} {G}{n}; rfl)'
    th.append(stmt); done.append(n)
th.append('\nend PRVEq.Port3_k2\n')
th.append('\n'.join(f'#print axioms PRVEq.Port3_k2.eq_{i}' for i in range(len(done))))
open('PRVEq_Port3_closures_k2.lean','w').write(fresh+'\n'.join(th)+'\n')
PY
