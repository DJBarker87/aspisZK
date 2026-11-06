import NKM_circle.Funs
import NHH_QAll
set_option autoImplicit false
noncomputable section
namespace NKM_FieldLaws
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open SamplerClosureProductExecution (encodeCM)
open NKM_circle

def encode (t : QM31Exact) : field.QM31 := fromQ (SamplerClosureProductExecution.encode t)
def Canon (t : field.QM31) : Prop := SamplerClosureProductCorrectness.Canonical (toQ t)

theorem roundtrip (t : field.QM31) (hc : Canon t) : encode (SamplerClosureProductCorrectness.decode (toQ t)) = t := by
 rw [encode,SamplerClosureProductCorrectness.encode_decode _ hc,from_to]

theorem canonical (t : QM31Exact) : Canon (encode t) := by
 unfold Canon encode
 rw [to_from]
 exact SamplerClosureProductCorrectness.encode_canonical t

theorem one : field.QM31.ONE = encode 1 := by
 unfold field.QM31.ONE encode fromQ fromCM
 exact congrArg fromQ SamplerClosureCircleFieldExecution.one

theorem zero : field.QM31.ZERO = encode 0 := by rfl

theorem square (t : QM31Exact) : field.QM31.square (encode t) = ok (encode (t*t)) := by
 simp only [field.QM31.square,encode,to_from,SamplerClosureCircleFieldExecution.square,bind_tc_ok]

theorem add (x y : QM31Exact) : field.QM31.add (encode x) (encode y) = ok (encode (x+y)) := by
 simp only [field.QM31.add,encode,to_from,SamplerClosureCircleFieldExecution.add,bind_tc_ok]

theorem sub (x y : QM31Exact) : field.QM31.sub (encode x) (encode y) = ok (encode (x-y)) := by
 simp only [field.QM31.sub,encode,to_from,SamplerClosureCircleFieldExecution.sub,bind_tc_ok]

theorem mul (x y : QM31Exact) : field.QM31.mul (encode x) (encode y) = ok (encode (x*y)) := by
 simp only [field.QM31.mul,encode,to_from,SamplerClosureProductCorrectness.public_product,bind_tc_ok]

theorem inverse_zero : field.QM31.try_inv (encode 0) = ok none := by
 simp only [field.QM31.try_inv,encode,to_from,SamplerClosureCircleFieldExecution.try_inverse_zero,bind_tc_ok,Option.map_none]

theorem inverse_nonzero (x : QM31Exact) (hx : x ≠ 0) :
 field.QM31.try_inv (encode x) = ok (some (encode x⁻¹)) := by
 simp only [field.QM31.try_inv,encode,to_from,SamplerClosureCircleFieldExecution.try_inverse_nonzero x hx,bind_tc_ok,Option.map_some]

/-- CLOSED inverse row association, with its full raw Result rather than a success premise. -/
theorem closed_inverse (x : NHH_QInverse.Q) :
 (do let o ← NFG_InverseRef.field.QM31.try_inv x; ok (o.map (fun v => fromQ (NHH_QInverse.toSampler v)))) =
 field.QM31.try_inv (fromQ (NHH_QInverse.toSampler x)) := by
 rw [field.QM31.try_inv,to_from,←NHH_QAll.try_association]
 simp only [bind_assoc_eq,bind_tc_ok]
 cases h : NFG_InverseRef.field.QM31.try_inv x <;> simp only [h,bind_tc_ok]
 case ok o => cases o <;> rfl

#print axioms roundtrip
#print axioms canonical
#print axioms one
#print axioms zero
#print axioms square
#print axioms add
#print axioms sub
#print axioms mul
#print axioms inverse_zero
#print axioms inverse_nonzero
#print axioms closed_inverse
end NKM_FieldLaws
end
