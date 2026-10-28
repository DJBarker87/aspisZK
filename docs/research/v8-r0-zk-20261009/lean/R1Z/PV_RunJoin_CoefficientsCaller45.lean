import R1Z.PV_RunJoin_CoefficientsVector45
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientsCaller45
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_CoefficientsVector45
variable [ExternalTypes]

-- Reducibility hints only; kernel checking and resource limits are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected

theorem complete (ops : ExternalFuns) (p : Nat → Nat → W) :
    ∃ out, @prover.opening_coefficients _ (ProverRwP6BodyCandidate.selected ops) .S2 (messages p) = .ok out ∧
      out.val = payload p 0 29 ∧ out.length = 29 := by
  obtain ⟨out,hout,hv⟩ := PV_RunJoin_CoefficientsVector45.complete ops p 29
    (alloc.vec.Vec.with_capacity Column (Slice.len (messages p))) 0#usize (by rfl)
    (by change 0+29 ≤ Usize.max;scalar_tac)
  have image : out.val = payload p 0 29 := by
    simpa only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl] using hv
  refine ⟨out,?_,image,?_⟩
  · unfold prover.opening_coefficients
    rw [PV_RunJoin_CoefficientsThread45.complete .S2 (messages p) _ 0#usize 29 (by
      rw [messages,Array.length_to_slice]
      change 29≤14336
      omega) (by
      change 0+29=(messages p).length
      rw [messages,Array.length_to_slice]
      rfl)]
    exact hout
  · change out.val.length = 29
    rw [image,payload_length]
#print axioms complete
end R1Z.PV_RunJoin_CoefficientsCaller45
