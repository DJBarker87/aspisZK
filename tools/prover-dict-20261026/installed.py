"""Compose every worker entry in one final dictionary, by field projections."""
from pathlib import Path
import re,sys
r=Path(__file__).resolve().parents[2];base=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PDict_Ordering
import R1Z.PDict_MaskError
import R1Z.PDict_RetryCap
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Installed
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := PDict_Ordering.selected

'''
t=(base/'PDict_Typenum.lean').read_text();ops=dict((int(i),v.strip()) for i,v in re.findall(r'op(\d+) := ([^\n,}]+)',t))
for i,v in sorted(ops.items()):
 if i in [184,194,204]:
  typ={184:'typenum.uint.UTerm',194:'typenum.bit.B1',204:'typenum.bit.B0'}[i]
  s+=f'theorem op{i}_installed (ops : ExternalFuns) (x : {typ}) :\n    (selected ops).op{i} x = .ok x := rfl\n\n'
 else:s+=f'theorem op{i}_installed (ops : ExternalFuns) :\n    (selected ops).op{i} = {v} := rfl\n\n'
for i in range(141,161):
 s+=f'''theorem op{i}_installed (ops : ExternalFuns) {{U B : Type}}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op{i} u b = PDict_Numeric.op{i} u b := rfl

'''
# Reuse the already checked typed statements, changing only the selected namespace.
for module in ['PDict_Compare','PDict_Primitives','PDict_Ordering']:
 t=(base/(module+'.lean')).read_text()
 for m in re.finditer(r'(?m)^theorem (op\d+_installed)\b',t):
  end=t.index('\n\n',m.start());block=t[m.start():end]
  block=block.replace('= lessEq cmp next a b','= PDict_Ordering.lessEq cmp next a b').replace('= less cmp next a b','= PDict_Ordering.less cmp next a b')
  s+=block+'\n\n'
s+='''theorem op256_installed (ops : ExternalFuns) (a b : r1_wire.Error) :
    (selected ops).op256 a b = .ok (decide (a=b)) := PDict_WireError.exact a b

/-- The actual emitted semantic-error continuation consumes this final selector. -/
theorem semantic_error (ops : ExternalFuns) (e : r1_wire.Error) :
    @prover.semantic_error _ (selected ops) e =
      .ok (match e with
        | .ActivePole => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  unfold prover.semantic_error
  change (do
    let b ← (selected ops).op256 e .ActivePole
    if b then .ok verifier.Error.Rejected else .ok verifier.Error.Semantic) = _
  rw [op256_installed]
  cases e <;> rfl

/-- Actual checker call, including its machine failure/divergence, is retained. -/
theorem public_check (ops : ExternalFuns) (v : transport.Variant)
    (ch : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
    (root : Array U8 32#usize) :
    @prover.public_check _ (selected ops) v ch root =
      (match v with
       | .S2 => do
         let (accepted,_) ← (selected ops).op232 ch
         if accepted then .ok (.Ok ()) else .ok (.Err verifier.Error.Rejected)
       | _ => .ok (.Err verifier.Error.Semantic)) := by
  cases v <;> rfl

'''
for name in re.findall(r'(?m)^theorem (\w+)',s):s+=f'#print axioms {name}\n'
s+='end R1Z.PDict_Installed\n'
p=base/'PDict_Installed.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('worker entries',len(re.findall(r'^theorem op',s,re.M)))
