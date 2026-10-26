import F3X_AccountReads
import F3W_CollisionFree
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Y_AccountMass
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

def Claims {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (P : ByteProver) (Q : Nat)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) : Prop :=
  (∀ H : Bytes → State,FS.firstReads FS.emptyTable (eval H (F3X_Account.program c hashv P)).1≤Q+1921) ∧
  F3T_AccountCharge.mass (F3X_Account.program c hashv P) F3X_Projection.project select Q≤F3T_Numeric.accountLoss Q

theorem budget {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (H : Bytes → State) : FS.firstReads FS.emptyTable
      (eval H (F3X_Account.program (F3V_Install.configuration base) hashv P)).1≤Q+1921 := by
  rw [←F3X_AccountPrior.actual _ hashv P H]
  apply F3X_AccountReads.bound base hashv (F3X_Account.prior P) (eval H P).2 Q _ D w H
  intro H
  rw [F3X_Account.prior_log]
  exact queries H

theorem claims {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    Claims (F3V_Install.configuration base) hashv P Q select := by
  have bound := budget base hashv D w P Q queries
  exact ⟨bound,F3T_AccountCharge.bound _ F3X_Projection.project select Q bound⟩

/-- The charged exception is not all oracle worlds. This is separate from
accepted-fixture existence: it does not claim an accepted collision-free H. -/
theorem clean {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (queries : ∀ H : Bytes → State,(eval H P).1.length≤0)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    ∃ H : Bytes → State,¬BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (0+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program (F3V_Install.configuration base) hashv P)
        F3X_Projection.project select)) :=
  F3W_CollisionFree.account_clean _ F3X_Projection.project select (budget base hashv D w P 0 queries)

#print axioms budget
#print axioms claims
#print axioms clean
end AspisR1.F3Y_AccountMass
end
