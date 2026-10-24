import Port16CUT_Driver
import Port6AUTH_Accounting
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port16CUT_Accounting
open Aeneas Aeneas.Std VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_Prefix Port15DRIVER_Local Port16CUT_Cuts

theorem budget (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    (weighted : delegatedWeight w ≤ 115) (adapter : AdapterRw.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (decoder : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).1
        ≤ Q+1161 := by
  exact Port6AUTH_Accounting.budget decoder
    (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash)
    P Q hq (driver_physical adapter _ D hash)
    (fun h i => Port16CUT_Driver.rust1161 ops reserved unwrap rest w budgets weighted adapter D hash h i) H

theorem log_length (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    (weighted : delegatedWeight w ≤ 115) (adapter : AdapterRw.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (decoder : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    (eval H (source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).1.length
        ≤ Q+2322 := by
  exact Port6AUTH_Accounting.log_length decoder
    (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash)
    P Q hq
    (fun h i => Port16CUT_Driver.rust1161 ops reserved unwrap rest w budgets weighted adapter D hash h i) H

#print axioms budget
#print axioms log_length
end AspisR1.Port16CUT_Accounting
end
