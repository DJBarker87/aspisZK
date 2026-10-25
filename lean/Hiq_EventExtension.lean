import Hist_JointCharge
import EndP_AuthMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_EventExtension
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem append_hit {I A : Type} [DecidableEq I] (bad : I → Table I A → A → Prop)
    (left right : List (I × A)) (T : Table I A) :
    hitsBad bad T left → hitsBad bad T (left ++ right) := by
  induction left generalizing T with
  | nil => intro h; exact False.elim h
  | cons head tail ih =>
    simp only [List.cons_append,hitsBad]
    intro h
    rcases h with first | rest
    · exact Or.inl first
    · exact Or.inr (ih _ rest)

/-- The old account/replay collision alternative is a subset of the ONE
new joint event. It is never union-charged as a second collision loss. -/
theorem replay_to_joint {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (q r : Nat) (le : q ≤ r) (H : Bytes → State) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv q
      (eval H (SdkC_Replay.augmented source project)) →
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv r
      (eval H (Hist_JointCharge.joint source project select)) := by
  intro hit
  have enlarged := EndP_AuthMass.event_mono (eval H (SdkC_Replay.augmented source project)) q r le hit
  rw [Hist_JointCharge.joint,Hist_AuditQueries.augmented_eval]
  exact append_hit _ _ _ _ enlarged

#print axioms append_hit
#print axioms replay_to_joint
end AspisR1.Hiq_EventExtension
end
