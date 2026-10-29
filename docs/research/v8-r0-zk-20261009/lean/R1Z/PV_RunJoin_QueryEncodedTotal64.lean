import R1Z.PV_RunJoin_QueryAccess64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryEncodedTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (folded : Slice aspis_core.field.wide_exact.WideExact)
    (size : 262144≤folded.length) (q : Usize) (bound : q.val<262144) :
    ∃ encoded, PV_RunJoin_QueryEncoded63.encode base heap box ops folded q=ok encoded ∧
      encoded.length=128 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨values,hvalues,hlen⟩ := PV_RunJoin_QueryAccess64.window folded size q bound
  obtain ⟨encoded,hr,hval,he⟩ := PV_RunJoin_EncodedComplete41.encode ops values
    (by rw [hlen];scalar_tac)
  refine ⟨encoded,?_,?_⟩
  · unfold PV_RunJoin_QueryEncoded63.encode
    rw [hvalues]
    change @prover.encoded_slice (types base) (selected base heap box ops) values=ok encoded
    rw [PV_RunJoin_EncodedInstalled48.complete base heap box ops]
    exact hr
  · rw [he,hlen]

#print axioms complete
end R1Z.PV_RunJoin_QueryEncodedTotal64
