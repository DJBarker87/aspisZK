import RPz7_EndP_Headline
import RPz7_DrvC_Implementation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Headline
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)

/-- EndP specialized to the constructed installed SDK driver. L157 and L159
remain precisely at this instance; this theorem alone does not supply them
or establish the native oracle-program transport. -/
theorem deployed_headline_installed {F C : Type}
    (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_Implementation.driver c))
    (binding : StoredCarrierBinding D (DrvC_Implementation.driver c) (lift P) runtime)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let source := GExp_Experiment.program
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      (DrvC_Installation.stage c) c.reserved c.boundaries c.std hashv
      (DrvC_Installation.currentDigest c) (DrvC_Installation.digest c) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100) := by
  exact EndP_Headline.deployed_headline D P Q0 Q1 hqueries
    (DrvC_Installation.sdk c) (DrvC_Implementation.implementation c)
    (DrvC_Installation.digest c) () runtime raw binding
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
    (DrvC_Installation.stage c) c.reserved c.boundaries c.std hashv
    (DrvC_Installation.currentDigest c) (DrvC_Installation.digest c)
    adversary chooseSecond prefixBound choiceBound project

#print axioms deployed_headline_installed
#print deployed_headline_installed
end AspisR1.DrvC_Headline
end
