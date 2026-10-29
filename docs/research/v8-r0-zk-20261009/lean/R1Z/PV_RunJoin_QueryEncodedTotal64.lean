import R1Z.PV_RunJoin_QueryAccess64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryEncodedTotal64
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
  · simp only [PV_RunJoin_QueryEncoded63.encode,hvalues,bind_tc_ok,
      PV_RunJoin_EncodedInstalled48.complete,hr]
  · rw [he,hlen]

#print axioms complete
end R1Z.PV_RunJoin_QueryEncodedTotal64
