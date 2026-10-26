import RPz7_F3T_Conditional
import RPz7_F3T_SourceCost
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ConditionalSum
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin F3T_Runtime

theorem bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (runtime : Runtime)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime)
    (account : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (accountBudget : ∀ H,firstReads emptyTable (eval H account).1≤Q+1921) :
    F3T_RuntimeBound.failureModel runtime+F3T_AccountCharge.mass account project select Q≤F3T_Numeric.total Q :=
  (add_le_add (F3T_RuntimeBound.failure_bound c D _ (F3T_Installed.physical c hashv) raw P Q queries runtime binding)
    (F3T_AccountCharge.bound account project select Q accountBudget)).trans_eq (F3T_Combined.arithmetic Q)

theorem zero_queries {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤0)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (runtime : Runtime)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime)
    (account : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (accountBudget : ∀ H,firstReads emptyTable (eval H account).1≤0+1921) :
    F3T_RuntimeBound.failureModel runtime+F3T_AccountCharge.mass account project select 0<1/(2:Rat)^100 :=
  (bound c D P 0 queries hashv runtime raw binding account project select accountBudget).trans_lt F3T_Numeric.zero_queries

#print axioms zero_queries
#print axioms bound
#print bound
end AspisR1.F3T_ConditionalSum
end
