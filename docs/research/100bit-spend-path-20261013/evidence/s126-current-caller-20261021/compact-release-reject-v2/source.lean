import CurrentCompactFirstCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.ReleaseReject
open AspisR1CurrentCaller FirstComposition

/-- TOTAL for every bad split, regardless of all child callbacks: no parser,
semantic verifier, allocation, digest or query operation is executed. -/
theorem tx1_bad_split (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (hk : k≠compact.SPLIT) :
    verifier.candidate.tx1 ops D pub bytes proof k hash obs=ok (.Err .Parse) := by
  unfold verifier.candidate.tx1
  have hb : (k != compact.SPLIT)=true := by simp only [bne_iff_ne];exact hk
  rw [hb]
  rfl

/-- Full Result at the release first_decoded error boundary. The error mapper
is retained, including its failure/divergence; no success premise is used. -/
theorem first_decoded_bad_split {E : Type} (ops : Ops)
    (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (pub : OldPublic) (bytes proof : Slice U8) (k : Usize) (hk : k≠compact.SPLIT) :
    AspisR1PublicPreparation.RepinS6First.first_decoded (currentTx1 ops D)
      error pub bytes proof k =
      (do let e ← error .Parse;ok (core.result.Result.Err e)) := by
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer currentTx1
  simp only [bind_tc_ok,Option.map_none]
  rw [tx1_bad_split ops D (toCurrentPublic pub) bytes proof k () none hk]
  rfl

/-- The adapter admits [3,11], but the frozen compact verifier rejects it.
This is derived from the actual SPLIT constant, not an input restriction. -/
theorem eleven_rejected {E : Type} (ops : Ops)
    (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (pub : OldPublic) (bytes proof : Slice U8) :
    AspisR1PublicPreparation.RepinS6First.first_decoded (currentTx1 ops D)
      error pub bytes proof 11#usize =
      (do let e ← error .Parse;ok (core.result.Result.Err e)) := by
  apply first_decoded_bad_split
  unfold compact.SPLIT
  scalar_tac

#print axioms tx1_bad_split
#print axioms first_decoded_bad_split
#print axioms eleven_rejected
end AspisR1CurrentCaller.ReleaseReject
