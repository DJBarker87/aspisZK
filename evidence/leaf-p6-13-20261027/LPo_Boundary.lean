import LPo_B_LPc_BoundaryProducer
import LPo_Readset
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.Boundary

/-- The exact scalar/vector fold result, including the second occurrence of
    coefficient zero, on the SAME array supplied by the caller's decoder. -/
theorem exact_result (p : Array aspis_core.field.QM31 28#usize) :
    r1_semantic.semantic_boundary p = (do
      let seed ← Array.index_usize p 0#usize
      ok (p.val.foldl LPo.BA.Add.field seed)) := by
  rw [← LPo.BA.Boundary.loop_eq_model, LPo.BA.Boundary.loop_pure]

/-- Successful decoding derives the invariant used by the native one-step
    harness. There is no extra canonicality hypothesis. -/
theorem decoded_exact (r : r1_wire.ValidatedRecord)
    (p : Array aspis_core.field.QM31 28#usize)
    (decoded : r1_wire.ValidatedRecord.decode_k 28#usize r 0#usize = ok (.Ok p)) :
    (∀ q ∈ p.val, LPo.BA.Add.Canonical q) ∧
    r1_semantic.semantic_boundary p = (do
      let seed ← Array.index_usize p 0#usize
      ok (p.val.foldl LPo.BA.Add.field seed)) ∧
    ∃ result, r1_semantic.semantic_boundary p = ok result ∧ LPo.BA.Add.Canonical result :=
  ⟨LPo.BC.Decode.success_canonical _ _ _ _ decoded, exact_result p,
    LPo.BC.Boundary.decoded_canonical r p decoded⟩

/-- Unique array identity, used to consume the SAME decoded native polynomial,
    not an independently selected canonical array. -/
theorem decoded_unique (r : r1_wire.ValidatedRecord)
    (p q : Array aspis_core.field.QM31 28#usize)
    (hp : r1_wire.ValidatedRecord.decode_k 28#usize r 0#usize = ok (.Ok p))
    (hq : r1_wire.ValidatedRecord.decode_k 28#usize r 0#usize = ok (.Ok q)) : p=q := by
  exact core.result.Result.Ok.inj (Result.ok.inj (hp.symm.trans hq))

/-- Caller round domain: the frozen non-prover call uses rows15..24. -/
theorem caller_row (round : Nat) (h : round<10) :
    15 ≤ 15+round ∧ 15+round ≤ 24 ∧ 14 ≤ 15+round := by omega

#print axioms exact_result
#print axioms decoded_exact
#print axioms decoded_unique
#print axioms caller_row
end LPo.Boundary
