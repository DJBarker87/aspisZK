import R1Z.PV_RunJoin_CoefficientListResult50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientsActual50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_CoefficientActualCell50 (Column permuted)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (messages : Slice Column) (small : messages.length≤14336) :
    ∃ coefficients : alloc.vec.Vec Column,
      @prover.opening_coefficients (types base) (selected base heap box ops) .S2 messages=ok coefficients ∧
      coefficients.val=messages.val.map permuted ∧ coefficients.length=messages.length := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨out,hout,hv⟩ := PV_RunJoin_CoefficientListResult50.complete messages.val
    (alloc.vec.Vec.with_capacity Column (Slice.len messages)) (by
      change 0+messages.val.length≤Usize.max
      have len : messages.val.length=messages.length := rfl
      rw [len]
      scalar_tac)
  have hval : out.val=messages.val.map permuted := by
    simpa only [alloc.vec.Vec.with_capacity,List.nil_append] using hv
  refine ⟨out,?_,hval,?_⟩
  · unfold prover.opening_coefficients
    rw [PV_RunJoin_CoefficientsThread45.complete .S2 messages _ 0#usize messages.length small (by change 0+messages.length=messages.length;omega),
      PV_RunJoin_CoefficientList50.complete base heap box ops messages messages.length _ 0#usize small (by change 0+messages.length=messages.length;omega)]
    simpa only [show (0#usize).val=0 from rfl,List.drop_zero] using hout
  · change out.val.length=messages.val.length
    rw [hval,List.length_map]
#print axioms complete
end R1Z.PV_RunJoin_CoefficientsActual50
