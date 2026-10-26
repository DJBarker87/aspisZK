import F3W_Rejection
import F3W_CollisionFree
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_Obstruction
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

/-- Exact installed-source counterexample family, with the actual bounded
account collision event absent. No model acceptance fixture is constructed. -/
theorem oversized_counterexample {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (s : Submission)
    (large : Aeneas.Std.Usize.max<s.publicBytes.length)
    (account : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (budget : ∀ H,firstReads emptyTable (eval H account).1≤0+1921) :
    ∃ H : Bytes → State,
      eval H (F3T_Installed.source c hashv (input c s))=([],false) ∧
      ¬BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (0+2965)
        (eval H (Hiq_RecordedJoint.program account project select)) ∧
      eval H (F3T_Installed.source c hashv (input c s))≠eval H (F3_Model.verifier D (input c s)) := by
  obtain ⟨H,clean⟩ := F3W_CollisionFree.account_clean account project select budget
  exact ⟨H,F3W_Rejection.oversized_eval c hashv s large H,clean,
    F3W_Rejection.oversized_ne c hashv s large D H⟩

/-- Allows a DIFFERENT complete account program for each submission, so the
obstruction does not depend on choosing an unrelated fixed account trace. -/
theorem no_unconditional_raw_join {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder)
    (account : Submission → Program Bytes State A)
    (project : Submission → A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : Submission → A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (budget : ∀ s H,firstReads emptyTable (eval H (account s)).1≤0+1921) :
    ¬∀ (s : Submission) (H : Bytes → State),
      eval H (F3T_Installed.source c hashv (input c s))=eval H (F3_Model.verifier D (input c s)) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (0+2965)
        (eval H (Hiq_RecordedJoint.program (account s) (project s) (select s))) := by
  intro join
  let s : Submission := ⟨List.replicate (Aeneas.Std.Usize.max+1) 0,[]⟩
  have large : Aeneas.Std.Usize.max<s.publicBytes.length := by
    simp only [s,List.length_replicate]
    omega
  obtain ⟨H,rejected,clean,different⟩ := oversized_counterexample c hashv D s large
    (account s) (project s) (select s) (budget s)
  rcases join s H with equal | collision
  · exact different equal
  · exact clean collision

#print axioms oversized_counterexample
#print axioms no_unconditional_raw_join
end AspisR1.F3W_Obstruction
end
