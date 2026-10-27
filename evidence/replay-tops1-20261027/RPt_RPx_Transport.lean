import RPt_RPx_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Transport
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

/-- All outcomes of the actual installed per-body source. This does not
silently constrain arbitrary external runtime histories. -/
def Claims {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (P : ByteProver) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    (∃ suffix : List (Bytes × State),
      (eval H (F3X_Account.program c hashv P)).1 =
        (eval H P).1 ++ (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1 ++ suffix) ∧
    FS.firstReads FS.emptyTable (eval H (F3X_Account.program c hashv P)).1 =
      FS.firstReads FS.emptyTable ((eval H P).1 ++
        (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1) ∧
    ((eval H P).1 ++ (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1).length≤Q+1921 ∧
    ((eval H (F3T_Installed.source c hashv (input c (eval H P).2))).2=false →
      eval H (F3X_Account.program c hashv P) =
        ((eval H P).1 ++ (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1,
          ((eval H P).2,none)))

theorem transport {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) :
    Claims (F3V_Install.configuration base) hashv P Q := by
  intro H
  exact ⟨RPx_Prefix.occurrences _ hashv P H,
    RPx_Accounting.exact base hashv D w P H,
    RPx_Accounting.attempted _ hashv P Q queries H,
    RPx_Rejected.adaptive _ hashv P H⟩

/-- SAME account bound used by the headline: source rejection cannot escape
its charge, and replay/audit adds the already allocated 1044 first reads. -/
theorem charged {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program (F3V_Install.configuration base) hashv P)
        F3X_Projection.project select)).1≤Q+2965) ∧
    F3T_AccountCharge.mass (F3X_Account.program (F3V_Install.configuration base) hashv P)
      F3X_Projection.project select Q≤F3T_Numeric.accountLoss Q := by
  have budget := F3Y_AccountMass.budget base hashv D w P Q queries
  exact ⟨F3T_AccountCharge.reads _ _ select Q budget,F3T_AccountCharge.bound _ _ select Q budget⟩

#print axioms transport
#print axioms charged
end AspisR1.RPx_Transport
end
