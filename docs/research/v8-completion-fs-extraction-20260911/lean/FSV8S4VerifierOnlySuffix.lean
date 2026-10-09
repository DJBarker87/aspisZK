import FSV8ExactRootCursor
import FSV8FreshTapeBudget
import FSV8BeforeAlphaMarkerFactorization
import FSV8ActualRootSourceFreshCap

/-! S4 UNCOMPILED concrete VERIFIER-only suffix. The inspected to_gamma()
reads the OOD rows from the already-parsed body. It does not invoke a prover
work callback between sampling a point and absorbing that row.
This is NOT a licence to remove adversary queries: they stay in the root's
blackBox execution. z/digest below are explicit suffix context, not assumed
fixed globally before the semantic transcript. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV8S4VerifierOnlySuffix
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle FSV8PostOODGammaScript
open AspisK1.V7FsAokExperiment AspisK1.V7FsStateRestorationCoupling
open FSV8ExactRootCursor FSV8FreshTapeBudget
open FSV8BeforeAlphaMarkerFactorization
noncomputable section
abbrev B := FSBoundedTranscript.Block
abbrev Pt := FSV7OODBodyScript.Point
abbrev K := FSNonzeroQM31.K

def firstReadOnly : Pt → Script (List UInt8) B Unit 0 := fun _ => .done ()
def secondReadOnly : Pt → Pt → Script (List UInt8) B Unit 0 := fun _ _ => .done ()

@[simp] theorem firstReadOnly_run (p : Pt)
    (tape : FSBoundedTranscript.Tape) (state : FSBoundedTranscript.Oracle) :
    run tape (firstReadOnly p) state = (some (),state) := rfl
@[simp] theorem secondReadOnly_run (p q : Pt)
    (tape : FSBoundedTranscript.Tape) (state : FSBoundedTranscript.Oracle) :
    run tape (secondReadOnly p q) state = (some (),state) := rfl

/-- Explicitly after points_absorb; no extra point-row absorb is inserted. -/
def selectedSuffix (z : Fin 10 → K) (cuts : RootCuts)
    (body : List UInt8) (digestAfterPoints : B) :=
  wholeStagedScript firstReadOnly secondReadOnly z cuts body digestAfterPoints

/-- Canonical parsed fields are 16-byte encodings. This read is justified
only on the real canonical-body path; malformed input is handled upstream. -/
def pointClaimBytes (body : List UInt8) : List UInt8 :=
  (body.drop (271*16)).take (87*16)

/-- Before points_absorb: preserve the real additional label-49 query. -/
def selectedSuffixBeforePoints (z : Fin 10 → K) (cuts : RootCuts)
    (body : List UInt8) (digestAfterSemantics : B) :=
  bind (absorbScript digestAfterSemantics 49 (pointClaimBytes body))
    (fun digestAfterPoints => selectedSuffix z cuts body digestAfterPoints)

theorem actual_no_work_budget :
    sourceThenGammaBudget 0 0 + beforeAlphaMarkerBudget + 9 = 1403 := by
  decide

theorem selected_work_profile : (0 : Nat)+0 ≤ 108 := by decide

/-- A FIXED-CONTEXT suffix configuration. This supplies the exact work and
adversary-fuel profile facts. For full soundness, use the dynamic-prelude root
rather than choosing this z/digest retrospectively from a completed run. -/
def fixedContextConfiguration
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : AspisK1.V7Tag73ExactCompilerResources.ExactCompilerResourceParameters)
    (blackBox : SameTapeBlackBox
      HiddenTape Observation (List UInt8))
    (tapeIdentity : HiddenTape → TapeIdentity) (observation : Observation)
    (adversaryLimits verifierLimits : AspisK1.V7FsAokExperiment.OracleLimits)
    (adversaryBound : adversaryLimits.totalCalls ≤
      AspisK1.V7Tag73ExactCompilerResources.globalFull256OracleCallCap parameters)
    (verifierBound : verifierLimits.totalCalls ≤
      AspisK1.V7Tag73ExactCompilerResources.globalFull256OracleCallCap parameters)
    (z : Fin 10 → K) (cuts : RootCuts) (digestAfterPoints : B) :
    Configuration HiddenTape TapeIdentity Observation
      (AspisK1.V7Tag73ExactCompilerResources.globalFull256OracleCallCap parameters) 0 0 where
  blackBox := blackBox
  tapeIdentity := tapeIdentity
  observation := observation
  adversaryLimits := adversaryLimits
  verifierLimits := verifierLimits
  adversaryFuel := parameters.q1ShaCallCap
  firstWork := firstReadOnly
  secondWork := secondReadOnly
  z := z
  cuts := cuts
  initialDigest := digestAfterPoints
  adversaryLimitBound := adversaryBound
  verifierLimitBound := verifierBound

#print axioms selectedSuffix
#print axioms actual_no_work_budget
#print axioms fixedContextConfiguration
end
end AspisV8Completion.FSV8S4VerifierOnlySuffix
