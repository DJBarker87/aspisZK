import S1TopPowersV1
import CheckpointBytes4SavedFields
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPowers
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisR1
open RetainedExactLimbCodec

/-- The checkpoint decoder's exact field carrier entails all eight machine
word bounds. No canonicality of attacker-supplied bytes is assumed. -/
theorem checkpoint_sourceE_canonical (x : OraclePortCheckpointAbiC5.E) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical
      (claimE (CheckpointBytes4ReaderFields.sourceE x)) := by
  let re := qm31ExactLimbEquiv.symm x.re
  let im := qm31ExactLimbEquiv.symm x.im
  change (((M31ParserRefinement.valueToU32 (re 0)).val < 2147483647 ∧
    (M31ParserRefinement.valueToU32 (re 1)).val < 2147483647) ∧
    ((M31ParserRefinement.valueToU32 (re 2)).val < 2147483647 ∧
    (M31ParserRefinement.valueToU32 (re 3)).val < 2147483647)) ∧
    (((M31ParserRefinement.valueToU32 (im 0)).val < 2147483647 ∧
    (M31ParserRefinement.valueToU32 (im 1)).val < 2147483647) ∧
    ((M31ParserRefinement.valueToU32 (im 2)).val < 2147483647 ∧
    (M31ParserRefinement.valueToU32 (im 3)).val < 2147483647))
  simp only [M31ParserRefinement.valueToU32_val]
  exact ⟨⟨⟨(re 0).isLt,(re 1).isLt⟩,⟨(re 2).isLt,(re 3).isLt⟩⟩,
    ⟨⟨(im 0).isLt,(im 1).isLt⟩,⟨(im 2).isLt,(im 3).isLt⟩⟩⟩

/-- At the lead's complete saved-field boundary the op17 input is canonical
by its SAME decoded gamma field. No independent range premise remains. -/
theorem resumed_powers_total_exact
    (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    ∃ out : Array Top.E 29#usize, powers 29#usize p.gamma=ok out ∧ ∀ j : Fin 29,
      AspisR1CurrentPreparedClaim.Concrete.Canonical
        (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt))) ∧
      AspisR1CurrentPreparedClaim.Concrete.decode
        (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt)))=
      AspisR1CurrentPreparedClaim.Concrete.decode (claimE p.gamma)^j.val := by
  apply powers_total_exact
  rw [fields.gamma]
  exact checkpoint_sourceE_canonical pm.gamma

/-- Concrete resume execution, with checkpoint input provenance retained.
The complete saved-field relation and gamma range are DERIVED from that same
successful return. There is no independent reader or powers success premise. -/
theorem concrete_resume_powers_total_exact (reserved : Bool) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (ck proof public1 : Slice U8) (hash : Hash)
    (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (H : MultiproofConeCanonical.Bytes → AspisV8R19.SourceDuplexStep.State)
    (stored pub : MultiproofConeCanonical.Bytes) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (encoding : MultiproofConeCanonical.bytesOf ck.val = OraclePortCheckpointAbiC5.encode H stored pub pm am)
    (success : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      D ck proof public1 .S2 hash=ok (.Ok (p,a))) :
    ∃ out : Array Top.E 29#usize, powers 29#usize p.gamma=ok out ∧ ∀ j : Fin 29,
      AspisR1CurrentPreparedClaim.Concrete.Canonical
        (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt))) ∧
      AspisR1CurrentPreparedClaim.Concrete.decode
        (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt)))=
      AspisR1CurrentPreparedClaim.Concrete.decode (claimE p.gamma)^j.val := by
  obtain ⟨fields⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof public1 .S2 hash p a success
  exact resumed_powers_total_exact p a pm am
    (CheckpointBytes4SavedFields.body_matches reserved ck p a fields H stored pub pm am encoding)

#print axioms checkpoint_sourceE_canonical
#print axioms resumed_powers_total_exact
#print axioms concrete_resume_powers_total_exact
end AspisS1TopPowers
