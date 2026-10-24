import Port17RELEASE_Driver
import Port6AUTH_Accounting
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Accounting
open FS FS2 FS2.Duplex R0C.V3
open Aeneas Aeneas.Std VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_Prefix Port17RELEASE_Prepare Port17RELEASE_Driver

theorem budget (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (decoder : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (source decoder
      (Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other) D hash) P)).1
        ≤ Q + 1161 + remainingWeight w := by
  let rust := Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other) D hash
  change firstReads emptyTable (eval H (source decoder rust P)).1 ≤ _
  rw [Port6AUTH_Accounting.first_reads decoder rust P (driver_physical adapter _ D hash) H,
    OraclePortFrozen2Join.originalWith_eval]
  have h := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H (canon (lift P))).1 ++ (eval H (rust (eval H (canon (lift P))).2)).1)
  rw [List.length_append] at h
  have hp : (eval H (canon (lift P))).1.length ≤ Q := by
    simpa only [canon_eval,lift_eval] using hq H
  have calls := Port17RELEASE_Driver.rust ops reserved unwrap base R B other w remaining
    adapter D hash H (eval H (canon (lift P))).2
  exact h.trans (by change _ ≤ Q + 1161 + remainingWeight w; omega)

theorem log_length (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (decoder : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    (eval H (source decoder
      (Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other) D hash) P)).1.length
        ≤ Q + 2322 + 2 * remainingWeight w := by
  let rust := Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other) D hash
  change (eval H (source decoder rust P)).1.length ≤ _
  rw [source_eval,OraclePortFrozen2Join.annotatedWith_eval]
  dsimp only [view]
  rw [List.length_append,OraclePortFrozen2Join.originalWith_eval]
  simp only [List.length_append]
  have hp : (eval H (canon (lift P))).1.length ≤ Q := by
    simpa only [canon_eval,lift_eval] using hq H
  have calls (i : Input) : (eval H (rust i)).1.length ≤ 1161 + remainingWeight w :=
    Port17RELEASE_Driver.rust ops reserved unwrap base R B other w remaining adapter D hash H i
  have h1 := calls (eval H (canon (lift P))).2
  have h2 := calls (enrich (build decoder (view (eval H (originalWith rust (canon (lift P))))))
    (eval H (originalWith rust (canon (lift P)))).2.1)
  simp only [OraclePortFrozen2Join.originalWith_eval,view] at h2
  omega

#print axioms budget
#print axioms log_length
end AspisR1.Port17RELEASE_Accounting
end
