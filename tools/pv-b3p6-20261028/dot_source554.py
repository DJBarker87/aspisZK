"""Independent source interpreter and bounded congruence proof of exact dot emission."""
from pathlib import Path
import re,sys,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';R=D/'resume18'
def emit(p,s):
 if '--check' in sys.argv: assert p.read_text()==s,str(p)
 else:p.write_text(s)
head='''namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
abbrev DotRaw554 := Array U64 4#usize
'''
s='import PV_B3P_DigestCpsEq9227\nimport PV_B3P_P227_01\n'+head+'''
def dot_cell554 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) (index : Usize)
    (raw : DotRaw554) : Result DotRaw554 := do
  let m ← Array.index_usize values index
  let value ← lift (UScalar.cast .U64 m)
  let weight ← Array.index_usize weights index
'''
for k,f in enumerate(['c0.a','c0.b','c1.a','c1.b']):
 s+=f'''  let limb{k} ← lift (UScalar.cast .U64 weight.{f})
  let product{k} ← lift (U64.wrapping_mul limb{k} value)
  let old{k} ← Array.index_usize {'raw' if k==0 else 'raw'+str(k)} {k}#usize
  let next{k} ← lift (U64.wrapping_add old{k} product{k})
  let raw{k+1} ← Array.update {'raw' if k==0 else 'raw'+str(k)} {k}#usize next{k}
'''
s+='  .ok raw4\n\ndef dot_reduce554 (raw sums : DotRaw554) : Result DotRaw554 := do\n'
for k in range(4):
 s+=f'''  let r{k} ← Array.index_usize raw {k}#usize
  let m{k} ← aspis_core.field.M31.reduce_u64 r{k}
  let value{k} ← lift (UScalar.cast .U64 m{k})
  let old{k} ← Array.index_usize {'sums' if k==0 else 'sums'+str(k)} {k}#usize
  let next{k} ← lift (U64.wrapping_add old{k} value{k})
  let sums{k+1} ← Array.update {'sums' if k==0 else 'sums'+str(k)} {k}#usize next{k}
'''
s+='''  .ok sums4

def dot_finish554 (sums : DotRaw554) : Result aspis_core.field.QM31 := do
  let r0 ← Array.index_usize sums 0#usize
  let m0 ← aspis_core.field.M31.reduce_u64 r0
  let r1 ← Array.index_usize sums 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 r1
  let c0 ← aspis_core.field.CM31.new m0 m1
  let r2 ← Array.index_usize sums 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 r2
  let r3 ← Array.index_usize sums 3#usize
  let m3 ← aspis_core.field.M31.reduce_u64 r3
  let c1 ← aspis_core.field.CM31.new m2 m3
  .ok { c0, c1 }

def dot_source554 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) : Result aspis_core.field.QM31 := do
  let sums := Array.repeat 4#usize 0#u64
  let raw := Array.repeat 4#usize 0#u64
'''
for j in range(4):s+=f'  let raw{j+1} ← dot_cell554 weights values {j}#usize '+('raw'if j==0 else f'raw{j}')+'\n'
s+='  let sums1 ← dot_reduce554 raw4 sums\n  let rawNext := Array.repeat 4#usize 0#u64\n'
for j in range(3):s+=f'  let rawNext{j+1} ← dot_cell554 weights values {j+4}#usize '+('rawNext'if j==0 else f'rawNext{j}')+'\n'
s+='  let sums2 ← dot_reduce554 rawNext3 sums1\n  dot_finish554 sums2\n\n#print axioms dot_source554\nend PV_B3P_Association554227\n'
emit(L/'PV_B3P_DotSourceDefs554227.lean',s)
# Normalize one bounded cell at a time using a named continuation law.
defs=s
cps='import PV_B3P_DotSourceDefs554227\nimport PV_B3P_Ordered227\n'+head
for helper,args in [('dot_cell554','weights values index raw'),('dot_reduce554','raw sums')]:
 decl=defs.split('def '+helper,1)[1].split('\ndef ',1)[0].split('\n#print',1)[0]
 binders,body=decl.split(' := do\n',1)
 binders=binders.split(' : Result DotRaw554')[0]
 body=body.rstrip().removesuffix('.ok raw4' if helper=='dot_cell554' else '.ok sums4')+'k '+('raw4' if helper=='dot_cell554' else 'sums4')+'\n'
 cps+='\ntheorem '+helper+'_continuation {β : Type}'+binders+' (k : DotRaw554 → Result β) :\n    (do let next ← '+helper+' '+args+'; k next) = (do\n'+body+') := by\n  simp only ['+helper+',PV_B3P_Ordered227.bind_assoc,bind_tc_ok]\n'
 cps+='\n#print axioms '+helper+'_continuation\n'
cps+='end PV_B3P_Association554227\n'
emit(L/'PV_B3P_DotContinuation554227.lean',cps)
# Only proof navigation uses actual reference syntax.
ref=(L/'PV_B3P_P227_01.lean').read_text();body=ref.split('def reference_field.qm31_m31_dot',1)[1].split('  := do\n',1)[1].split('\n\n')[0]
lines=body.splitlines(); binders=[(i,re.match(r'  let (\w+) ←',v)[1]) for i,v in enumerate(lines) if re.match(r'  let (\w+) ←',v)]
s='import PV_B3P_DotContinuation554227\nimport PV_B3P_LinkDefinitions13227\nimport Lean.Elab.Tactic.AsAuxLemma\n'+head+'''
attribute [local irreducible] Aeneas.Std.bind Array.index_usize Array.update
  U64.wrapping_add U64.wrapping_mul aspis_core.field.M31.reduce_u64
  aspis_core.field.CM31.new

theorem dot_source_reference554 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) :
    dot_source554 weights values = reference_field.qm31_m31_dot weights values := by
  unfold dot_source554 reference_field.qm31_m31_dot
'''
indent='  ';counts=[23]*4+[24]+[23]*3+[24,10];n=0
for j,count in enumerate(counts):
 s+=indent+'as_aux_lemma =>\n';indent+='  '
 s+=indent+('rw [dot_cell554_continuation]\n' if j in [0,1,2,3,5,6,7] else 'rw [dot_reduce554_continuation]\n' if j in [4,8] else 'unfold dot_finish554\n')
 for k in range(count):
  i,name=binders[n];n+=1
  s+=indent+'apply bind_equal9\n'+indent+'intro '+name+'\n'
 s+=indent+'simp only [bind_tc_ok]\n'
assert n==len(binders)
s+=indent+'rfl\n\ntheorem dot_source_link554 :\n    PV_B3P_Links13227.PV_B3P_Link_field_qm31_m31_dot dot_source554 :=\n  funext fun weights => funext (dot_source_reference554 weights)\n\n#print axioms dot_source_reference554\n#print axioms dot_source_link554\nend PV_B3P_Association554227\n'
emit(L/'PV_B3P_DotSource554227.lean',s)
print(json.dumps(dict(reference_monadic_steps=len(binders),maximum_stage=24,independent_source=True)))
