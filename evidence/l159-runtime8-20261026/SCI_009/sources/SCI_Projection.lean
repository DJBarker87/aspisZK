import SCI_SameWorld
import F3X_Join
import SCH_RecorderProjection
import SCH_EventKnownSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCI_Projection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Expand the ACTUAL heterogeneous recorder, exposing the selected replay
and all four selected physical audit reads. No query/log identity is assumed. -/
theorem recorder_log {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    (eval H (Hiq_RecordedJoint.program source project select)).1 =
      (eval H source).1 ++
      (eval H (SdkC_Replay.replay (project (eval H source).2).1
        (project (eval H source).2).2)).1 ++
      (eval H (Hist_AuditQueries.audit (select (eval H source).2).1
        (select (eval H source).2).2)).1 := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,
    Hist_AuditQueries.augmented,SdkC_Replay.augmented,
    OracleProgramRecording.eval_record,eval_bind,eval,List.append_nil,List.append_assoc]

/-- An equality of recorder logs necessarily identifies the LAST physical
public audit input. Sharing one oracle world alone cannot imply this. -/
theorem final_audit {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    (eval H (Hiq_RecordedJoint.program source project select)).1.getLast? =
      some ((select (eval H source).2).2.pub,H (select (eval H source).2).2.pub) := by
  rw [recorder_log,Hist_AuditQueries.audit_eval]
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,Option.some_or]

/-- Concrete obstruction at the two requested recorder carriers: unequal
selected current-public audit bytes forbid ordered-log equality, regardless
of common H or of the earlier source/preparation/replay traces. This does
not claim that equal collision events require equal full logs. -/
theorem selected_audit_obstruction {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State)
    (prior : Program Bytes State Unit) (s : F3T_ByteCarrier.Submission)
    (lp : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (rp : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (rs : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (different : (lp (eval H (F3X_AccountPrior.program c hashv prior s)).2).2.pub ≠
      (rs (eval H (SCE_Experiment.account c hashv copy allocator id a)).2).2.pub) :
    (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
      F3X_Projection.project lp)).1 ≠
    (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account c hashv copy allocator id a)
      rp rs)).1 := by
  intro same
  have last := congrArg List.getLast? same
  rw [final_audit,final_audit] at last
  exact different (congrArg Prod.fst (Option.some.inj last))

/-- The F3X prior/submission specialization is on the SAME adaptive prover.
This closes that specialization only; it does not identify it with SCE's
physical account recorder. -/
theorem prior_event (iv : State) (Q : Nat) {F C : Type}
    (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : F3T_ByteCarrier.ByteProver) (H : Bytes → State)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    BinRawByteCollisionTargets.event iv Q
      (eval H (Hiq_RecordedJoint.program
        (F3X_AccountPrior.program c hashv (F3X_Account.prior P) (eval H P).2)
        F3X_Projection.project select)) ↔
    BinRawByteCollisionTargets.event iv Q
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P)
        F3X_Projection.project select)) := by
  have actual := F3X_AccountPrior.actual c hashv P H
  exact SCH_RecorderProjection.event _ _ _ _
    (SCH_RecorderProjection.logs _ _ _ _ _ _ H (congrArg Prod.fst actual)
      (congrArg F3X_Projection.project (congrArg Prod.snd actual))
      (congrArg select (congrArg Prod.snd actual)))

/-- Inhabit the audit obstruction on the actual F3X and SCE recorder carriers.
The source is arbitrary; no crypto acceptance is claimed. -/
theorem different_audits {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State)
    (prior : Program Bytes State Unit) (s : F3T_ByteCarrier.Submission)
    (rp : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
      F3X_Projection.project (fun _ => (⟨[],[]⟩,⟨[],[]⟩)))).1 ≠
    (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account c hashv copy allocator id a)
      rp (fun _ => (⟨[],[]⟩,⟨[],[0]⟩)))).1 := by
  apply selected_audit_obstruction
  intro same
  cases same

namespace OrderWitness
open FS AspisV8PairedCommitment
abbrev zero : State := fun _ => 0
abbrev one : State := fun _ => 1
abbrev two : State := fun _ => 2
def address : Bytes := bytes one

theorem nonempty : address ≠ [] := by
  intro same
  have length := congrArg List.length same
  rw [address,bytes_length] at length
  cases length

theorem child_none (input : Bytes) (short : input.length < 65) (j : Fin 2) :
    BinRawByteCollisionTargets.child j input = none := by
  have different : BinMerkle32Path.nodeInput (BinMerkleNodeCodec.readChildren input) ≠ input := by
    intro same
    have length := congrArg List.length same
    simp only [BinMerkle32Path.nodeInput,BinMerkle32Path.nodeBytes,List.length_cons,List.length_ofFn] at length
    omega
  simp only [BinRawByteCollisionTargets.child,BinMerkleNodeCodec.parse,if_neg different,
    Option.map_none]

theorem empty_pred (j : Fin 5) : BinRawByteCollisionTargets.pred j [] = none := by
  have child : ∀ i, BinRawByteCollisionTargets.child i [] = none :=
    fun i => child_none [] (by decide) i
  fin_cases j <;> simp [BinRawByteCollisionTargets.pred,child,
    BinRawByteCollisionTargets.trailing,BinRawByteCollisionTargets.fixed]

theorem address_pred (j : Fin 5) :
    BinRawByteCollisionTargets.pred j address = none ∨
    BinRawByteCollisionTargets.pred j address = some one := by
  have length : address.length = 32 := bytes_length _
  have child : ∀ i, BinRawByteCollisionTargets.child i address = none :=
    fun i => child_none address (by omega) i
  have headPred : BinRawByteCollisionTargets.fixed 0 address = some one := by
    simpa only [address,List.nil_append,List.append_nil] using
      BinRawByteCollisionTargets.fixed_frame 0 [] one [] rfl
  have tail : BinRawByteCollisionTargets.trailing address = some one := by
    simpa only [address,List.nil_append] using BinRawByteCollisionTargets.trailing_frame [] one
  have middlePred : BinRawByteCollisionTargets.fixed 38 address = none := by
    simp only [BinRawByteCollisionTargets.fixed,length]; decide
  fin_cases j <;> simp [BinRawByteCollisionTargets.pred,child,headPred,tail,middlePred]

/-- The actual five-target event changes under reordering the SAME two
consistent reads in the SAME oracle world. This rules out replacing ordered
first-read association by set containment or common-H rhetoric. -/
theorem reordered_event :
    ∃ H : Bytes → State,
      (∀ q ∈ ([(address,two),([],one)] : List (Bytes × State)), q.2 = H q.1) ∧
      (∀ q ∈ ([( [],one),(address,two)] : List (Bytes × State)), q.2 = H q.1) ∧
      BinRawByteCollisionTargets.event zero 2 ([(address,two),([],one)],()) ∧
      ¬ BinRawByteCollisionTargets.event zero 2 ([( [],one),(address,two)],()) := by
  let H : Bytes → State := fun a => if a = [] then one else two
  have oneZero : one ≠ zero := by intro h; have evaluated :=  congrFun h 0; exact (by decide : (1 : AspisV8R19.DuplexFrames.Byte) ≠ 0) evaluated
  have twoZero : two ≠ zero := by intro h; have evaluated :=  congrFun h 0; exact (by decide : (2 : AspisV8R19.DuplexFrames.Byte) ≠ 0) evaluated
  have twoOne : two ≠ one := by intro h; have evaluated :=  congrFun h 0; exact (by decide : (2 : AspisV8R19.DuplexFrames.Byte) ≠ 1) evaluated
  have notTarget (j : Fin 5) : BinRawByteCollisionTargets.pred j address ≠ some two := by
    rcases address_pred j with none | someOne
    · rw [none]; intro same; cases same
    · rw [someOne]; intro same; exact twoOne (Option.some.inj same).symm
  refine ⟨H,?_,?_,?_,?_⟩
  · intro q member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp only [H,nonempty,if_false,if_true]
  · intro q member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp only [H,nonempty,if_false,if_true]
  · change hitsBad _ _ _
    rw [hitsBad.eq_2,hitsBad.eq_2]
    right
    left
    refine ⟨?_,?_,Or.inr (Or.inr ⟨4,address,Or.inr ?_,?_⟩)⟩
    · simp only [AspisV8PairedCommitment.put,Ne.symm nonempty,if_false,emptyTable]
    · refine ⟨{address},by simp,?_⟩
      intro b known
      by_cases same : b = address
      · exact Finset.mem_singleton.mpr same
      · exact False.elim (known (by simp only [AspisV8PairedCommitment.put,if_neg same,emptyTable]))
    · simp only [AspisV8PairedCommitment.put,ite_true,ne_eq,Option.some_ne_none,not_false_eq_true]
    · rw [BinRawByteCollisionTargets.pred_prefix]
      simpa only [address,List.nil_append,List.append_nil] using
        BinRawByteCollisionTargets.fixed_frame 0 [] one [] rfl
  · change ¬ hitsBad _ _ _
    simp only [hitsBad.eq_2,hitsBad.eq_1,or_false]
    rintro (⟨_,_,bad⟩ | ⟨_,_,bad⟩)
    · rcases bad with same | ⟨b,previous⟩ | ⟨j,b,known,target⟩
      · exact oneZero same
      · cases previous
      · rcases known with rfl | known
        · rw [empty_pred] at target; cases target
        · exact known rfl
    · rcases bad with same | ⟨b,previous⟩ | ⟨j,b,known,target⟩
      · exact twoZero same
      · by_cases same : b = []
        · simp only [AspisV8PairedCommitment.put,if_pos same] at previous
          exact twoOne (Option.some.inj previous).symm
        · simp only [AspisV8PairedCommitment.put,if_neg same,emptyTable] at previous
          cases previous
      · rcases known with rfl | known
        · exact notTarget j target
        · by_cases same : b = []
          · subst b
            rw [empty_pred] at target
            cases target
          · exact known (by simp only [AspisV8PairedCommitment.put,if_neg same,emptyTable])

#print axioms nonempty
#print axioms child_none
#print axioms empty_pred
#print axioms address_pred
#print axioms reordered_event
end OrderWitness

#print axioms recorder_log
#print axioms final_audit
#print axioms selected_audit_obstruction
#print axioms prior_event
#print axioms different_audits
end AspisR1.SCI_Projection
end
