import EndP_Endpoint
import EndP_AuthMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_Headline
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)

/-- Conditional deployed Claims and conservative accounting for the exact
AuS1 alternative on the explicit GExp source. No independence is assumed.
The sum is an accounting upper bound, not an assertion that the native
AuS1 preparation prefix equals this whole experiment's trace. That source
association remains with L157/L159; no new global equality is assumed here. -/
theorem deployed_headline
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (adapter : AdapterRw.Ops) (impl : VTop_OracleCode.Implementation) {Hash : Type}
    (digest : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (Port1_Driver.rust adapter impl digest hash))
    (binding : StoredCarrierBinding D (Port1_Driver.rust adapter impl digest hash) (lift P) runtime)
    (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let source := GExp_Experiment.program current stage reserved B std hashv D1 D2 adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100) := by
  dsimp only
  have claims := EndP_Endpoint.final_soundness D P (Q0+Q1) hqueries
    adapter impl digest hash runtime raw binding
  have auth := EndP_AuthMass.bound
    (GExp_Experiment.program current stage reserved B std hashv D1 D2 adversary chooseSecond)
    project (Q0+Q1)
    (GExp_CollisionBudget.first_reads current stage reserved B std hashv D1 D2 adversary chooseSecond
      Q0 Q1 prefixBound choiceBound)
  have total := (add_le_add claims.2.2.2.1 auth).trans_eq (EndP_Numeric.total_eq (Q0+Q1)).symm
  refine ⟨claims,total,?_⟩
  intro zero
  apply total.trans
  rw [zero]
  exact EndP_Numeric.zero_queries

#print axioms deployed_headline
#print deployed_headline
end AspisR1.EndP_Headline
end
