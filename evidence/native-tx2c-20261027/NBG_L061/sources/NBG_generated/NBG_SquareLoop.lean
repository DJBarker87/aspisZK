import SAQ_SquareSourceModel
import LPf_BaseMultiply
set_option autoImplicit false
noncomputable section
namespace NBG_SquareLoop
open Aeneas Aeneas.Std Result AspisR1
open AspisR1M31Inverse.SquareProof

theorem mul_total : TotalMul FIo_Native.aspis_core.field.M31.mul := by
  intro x y
  obtain ⟨z,run,_,_⟩ := LPf_BaseMultiply.source x y
  exact ⟨z,run⟩

theorem mul_refines : RefinesMul FIo_Native.aspis_core.field.M31.mul := by
  intro x y z run
  obtain ⟨out,call,value,_⟩ := LPf_BaseMultiply.source x y
  have same : out = z := Result.ok.inj (call.symm.trans run)
  subst out
  change (z.val : ZMod 2147483647) = (x.val : ZMod 2147483647) * (y.val : ZMod 2147483647)
  rw [value]
  simp

/-- Reuses the existing symbolic range induction. Every raw32-bit initial
value and every machine count are allowed; no successful return is assumed. -/
theorem square_n_result (value : U32) (count : Usize) :
    ∃ out, AspisR1M31Inverse.field.square_n
        FIo_Native.aspis_core.field.M31.mul value count = ok out ∧
      R17CurrentM31Semantics.decode out =
        R17CurrentM31Semantics.decode value ^ (2 ^ count.val) :=
  square_n_total_model _ mul_total mul_refines value count

#print axioms mul_total
#print axioms mul_refines
#print axioms square_n_result
#print axioms AspisR1.LPf_BaseMultiply.source
end NBG_SquareLoop
