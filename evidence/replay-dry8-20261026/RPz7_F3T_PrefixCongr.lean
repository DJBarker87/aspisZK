import RPz7_F3T_AlignedRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_PrefixCongr
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem verifierFrom_congr (D : LiteralByteProtocol.Decoder)
    (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (pf pf' : LiteralProtocol.Proof)
    (same : ∀ i,i<33 → LiteralTranscript.erase (pf' i)=LiteralTranscript.erase (pf i))
    (n : Nat) (below : n≤33) (a b : LiteralTranscript.Prefix)
    (samePrefix : LiteralTranscript.erasePrefix a=LiteralTranscript.erasePrefix b) :
    OracleDecisionFeasibilityCore.verifierFrom D (F3_Model.decision physical stored) pf' n a=
      OracleDecisionFeasibilityCore.verifierFrom D (F3_Model.decision physical stored) pf n b := by
  induction n generalizing a b with
  | zero=>
    change F3_Model.decision physical stored (LiteralTranscript.erasePrefix a) (LiteralTranscript.erase (pf' 33))=
      F3_Model.decision physical stored (LiteralTranscript.erasePrefix b) (LiteralTranscript.erase (pf 33))
    rw [samePrefix];rfl
  | succ n ih=>
    have index : 33-(n+1)<33 := by omega
    have rows := same _ index
    change bind (LiteralByteSampler.samp (33-(n+1)) a (pf' (33-(n+1)))).toProgram _=
      bind (LiteralByteSampler.samp (33-(n+1)) b (pf (33-(n+1)))).toProgram _
    have sampler : LiteralByteSampler.samp (33-(n+1)) a (pf' (33-(n+1)))=
        LiteralByteSampler.samp (33-(n+1)) b (pf (33-(n+1))) := by
      unfold LiteralByteSampler.samp LiteralTranscript.samp
      rw [samePrefix,rows]
    rw [sampler]
    congr 1
    funext c
    apply ih (by omega)
    rw [LiteralTranscript.erasePrefix_ext,LiteralTranscript.erasePrefix_ext,samePrefix,rows]

theorem verifier_congr (D : LiteralByteProtocol.Decoder) (i j : F3_Model.Input)
    (semantic : i.semantic=j.semantic) (physical : i.physical=j.physical) (stored : i.stored=j.stored)
    (same : ∀ row,row<33 → LiteralTranscript.erase (i.proof row)=LiteralTranscript.erase (j.proof row)) :
    F3_Model.verifier D i=F3_Model.verifier D j := by
  unfold F3_Model.verifier OraclePortStoredExperimentC4.verifier
  rw [semantic,physical,stored]
  exact verifierFrom_congr D j.physical j.stored j.proof i.proof same 33 (by omega) _ _ rfl

#print axioms verifier_congr
#print axioms verifierFrom_congr
end AspisR1.F3T_PrefixCongr
end
