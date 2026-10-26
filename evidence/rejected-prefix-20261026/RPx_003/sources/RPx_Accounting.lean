import RPx_Rejected
import F3Y_AccountMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Accounting
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

/-- Exact duplicate policy: the account and prior-plus-source have the same
number of first reads, on every outcome; cached preparation adds none. -/
theorem exact {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (H : Bytes → State) :
    FS.firstReads FS.emptyTable (eval H (F3X_Account.program (F3V_Install.configuration base) hashv P)).1 =
    FS.firstReads FS.emptyTable ((eval H P).1 ++
      (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv
        (input (F3V_Install.configuration base) (eval H P).2))).1) := by
  rw [←F3X_AccountPrior.actual _ hashv P H,
    F3X_AccountReads.reused base hashv (F3X_Account.prior P) (eval H P).2 H D w,
    F3X_Account.prior_log]

/-- Occurrences, including duplicates, are bounded separately from distinct
reads. This prevents treating deduplication as deletion of actual queries. -/
theorem attempted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State) :
    ((eval H P).1 ++ (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1).length≤Q+1921 := by
  rw [List.length_append]
  exact Nat.add_le_add (queries H) (F3X_SourceBudget.source c hashv _ H)

/-- On rejection the account has exactly the source occurrence count, not
just a first-read upper bound. The all-outcome source bound covers early exits. -/
theorem rejected_length {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State)
    (rejected : (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).2=false) :
    (eval H (F3X_Account.program c hashv P)).1.length =
      (eval H P).1.length + (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1.length ∧
    (eval H (F3X_Account.program c hashv P)).1.length≤Q+1921 := by
  rw [RPx_Rejected.adaptive c hashv P H rejected]
  exact ⟨List.length_append,attempted c hashv P Q queries H⟩

#print axioms exact
#print axioms attempted
#print axioms rejected_length
end AspisR1.RPx_Accounting
end
