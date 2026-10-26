import F3U_ConditionalBound
import F3U_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AccountEndpoint
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_Runtime F3U_CollisionJoin

/-- CONDITIONAL endpoint: the all-byte collision-aware source join is still
an explicit premise. This theorem is not deployed_candidate. -/
theorem bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
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
    F3T_RuntimeBound.failureModel runtime≤F3T_Numeric.total Q := by
  apply F3U_ConditionalBound.bound c D P Q queries hashv runtime _ join binding account project select accountBudget
  intro H collision
  exact F3U_AccountEvent.charged account project select Q accountBudget H collision

#print axioms bound
end AspisR1.F3U_AccountEndpoint
end
