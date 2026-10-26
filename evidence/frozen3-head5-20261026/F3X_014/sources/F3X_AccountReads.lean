import F3X_AccountPrior
import F3X_ReadInclusion
import F3X_SourceBudget
import F3W_Runs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_AccountReads
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

theorem reused {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (s : Submission) (H : Bytes → State)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words) :
    let c := F3V_Install.configuration base
    FS.firstReads FS.emptyTable (eval H (F3X_AccountPrior.program c hashv prior s)).1=
      FS.firstReads FS.emptyTable ((eval H prior).1++
        (eval H (F3T_Installed.source c hashv (input c s))).1) := by
  dsimp only
  let c := F3V_Install.configuration base
  rw [F3X_AccountPrior.evaluation]
  change FS.firstReads FS.emptyTable ((eval H prior).1++(eval H (F3X_Account.submitted c hashv s)).1)=
    FS.firstReads FS.emptyTable ((eval H prior).1++(eval H (F3T_Installed.source c hashv (input c s))).1)
  by_cases success : (eval H (F3T_Installed.source c hashv (input c s))).2=true
  · obtain ⟨e,first⟩ := F3W_Runs.accepted base hashv s H D w success
    rw [F3X_Account.accepted c base.boundaries s H e hashv success]
    simp only [Prod.fst]
    rw [←List.append_assoc]
    apply OracleProgramRecording.firstReads_append_reused
    intro a read
    have sourceRead := F3X_ReadInclusion.preparation c base.boundaries s H e hashv first a read
    change a∈(_++_).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_right _ sourceRead
  · have rejected : (eval H (F3T_Installed.source c hashv (input c s))).2=false := Bool.eq_false_iff.mpr success
    simp only [F3X_Account.submitted,eval_bind,rejected,Bool.false_eq_true,ite_false,eval,List.append_nil]

theorem bound {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (s : Submission) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H prior).1.length≤Q)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words) (H : Bytes → State) :
    FS.firstReads FS.emptyTable
      (eval H (F3X_AccountPrior.program (F3V_Install.configuration base) hashv prior s)).1≤Q+1921 := by
  rw [reused base hashv prior s H D w]
  apply (VerifierCallBudget.firstReads_le_length _ _).trans
  rw [List.length_append]
  exact Nat.add_le_add (queries H) (F3X_SourceBudget.source _ hashv s H)

#print axioms reused
#print axioms bound
end AspisR1.F3X_AccountReads
end
