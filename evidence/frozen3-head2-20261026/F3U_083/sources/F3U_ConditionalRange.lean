import F3U_AccountEndpoint
import F3U_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ConditionalRange
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_TwoPass F3T_ByteCarrier F3T_Runtime F3U_CollisionJoin

theorem claims {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (runtime : Runtime)
    (account : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (accountBudget : ∀ H,firstReads emptyTable (eval H account).1≤Q+1921)
    (join : Join c D (F3T_Installed.source c hashv) (fun H _ _=>
      AuS1_Finish.Collision H (eval H account).1 (project (eval H account).2).1 (project (eval H account).2).2))
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime) :
    F3T_RuntimeBound.failureModel runtime≤F3T_Numeric.total Q ∧
    (Q≤F3U_RangeEdges.maxQueries → F3T_RuntimeBound.failureModel runtime≤(Q+1:Rat)*(1/(2:Rat)^100)) ∧
    (Q=0 → F3U_Numeric.margin≤1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
      F3T_RuntimeBound.failureModel runtime<1/(2:Rat)^100) := by
  have bound := F3U_AccountEndpoint.bound c D P Q queries hashv runtime account project select accountBudget join binding
  refine ⟨bound,fun range=>bound.trans (F3U_Range.per_attempt Q range),?_⟩
  intro zero
  subst Q
  exact F3U_Numeric.runtime_margin _ bound

#print axioms claims
end AspisR1.F3U_ConditionalRange
end
