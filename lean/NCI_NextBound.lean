import CheckpointBytes4Ops
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_NextBound
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Ops

theorem guard {T : Type} (condition : Prop) [Decidable condition]
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if condition then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    ¬condition ∧ tail=ok (.Ok out) := by
  by_cases hc : condition
  · simp only [if_pos hc] at h
    cases h
  · exact ⟨hc,by simpa only [if_neg hc] using h⟩

theorem successful_header (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (ck proof publicInput : Slice U8) (hash : H)
    (v : transport.Variant) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (ops reserved) D ck proof publicInput v hash = ok (.Ok (p,a))) :
    ∃ b : U8, Slice.index_usize ck 9#usize = ok b ∧ b.val≤22 := by
  unfold verifier.resumeWithOps at success
  obtain ⟨_,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  obtain ⟨_,h⟩ := guard _ _ _ h
  obtain ⟨_,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨_,h⟩ := guard _ _ _ h
  obtain ⟨_,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨_,h⟩ := guard _ _ _ h
  obtain ⟨b,read,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨bound,_⟩ := guard _ _ _ h
  refine ⟨b,read,?_⟩
  change ¬b.val > 22 at bound
  omega

theorem successful_next (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (ck proof publicInput : Slice U8) (hash : H)
    (v : transport.Variant) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (ops reserved) D ck proof publicInput v hash = ok (.Ok (p,a))) :
    a.next.val≤22 := by
  obtain ⟨b,read,bound⟩ := successful_header reserved D ck proof publicInput hash v p a success
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof publicInput v hash p a success
  have same : b=f.nextByte := Result.ok.inj (read.symm.trans f.nextRead)
  have cast : UScalar.cast .Usize f.nextByte = a.next := Result.ok.inj f.nextCast
  rw [←cast]
  simp only [UScalar.cast]
  change (f.nextByte.bv.setWidth System.Platform.numBits).toNat≤22
  rw [BitVec.toNat_setWidth_of_le (by rcases System.Platform.numBits_eq with h|h <;> omega)]
  simpa [same] using bound
#print axioms guard
#print axioms successful_header
#print axioms successful_next
end AspisR1.NCI_NextBound
