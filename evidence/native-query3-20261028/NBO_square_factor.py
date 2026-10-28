from pathlib import Path
D=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean'
s=(D/'NBO_QueryFactor.lean').read_text();a=s.index('  let we6 ←',s.index('def suffix'));b=s.index('  let m ← ops.op7 z z',a);c=s.index('  let m1 ←',b);e=s.index('\nprivate theorem',c)
before=s[a:b];after=s[c:e]
head='''import NBO_QueryRhs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_SquareCut
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Exact reached line and geometry prefix before scalar multiplication. -/
def before (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) : Result (Stage2E × U32) := do
'''
mid='''  ok (folded1,z)
/-- Exact emitted continuation AFTER the SAME scalar multiply returns.
The value m is a reached child return; no arithmetic is silently replaced. -/
def after (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (pending : verifier.BatchedWeights)
 (folded1 : Stage2E) (m : U32) :
 Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) := do
'''
tail='''
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
 cases x <;> rfl
/-- Total Result fission at the actual pure field-call boundary. -/
theorem association (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize) :
 NBO_QueryFactor.suffix ops p a obs geometry pending values inverse =
 (do let (line,z) ← before ops p a geometry values inverse
     let square ← ops.op7 z z
     after ops p a obs pending line square) := by
 unfold NBO_QueryFactor.suffix before after
 simp only [associate,bind_tc_ok]
#print axioms associate
#print axioms association
end NBO_SquareCut
end
'''
(D/'NBO_SquareCut.lean').write_text(head+before+mid+after+tail)
