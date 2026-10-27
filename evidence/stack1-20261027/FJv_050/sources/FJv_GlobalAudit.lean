import FJv_Nonvacuity
import FJv_GlobalOwners
import Lean
import FIp_Remaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJv_OwnerLeaf
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open R3SemanticEquationCore R3SemanticRemainingJoins

@[reducible] def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FJu_Remaining.Endpoint input.decoded (typedRows parsed q tr) input.data
end AspisR1.FJv_OwnerLeaf
end
open Lean Meta Elab
run_meta do
  let old ← getConstInfo ``AspisR1.FJu_GlobalOwners.Owners
  let fresh ← getConstInfo ``AspisR1.FJv_GlobalOwners.Owners
  let some before := old.value? true | throwError "Missing old global owner body"
  let some after := fresh.value? true | throwError "Missing new global owner body"
  let candidate ← mkConstWithFreshMVarLevels ``AspisR1.FJv_GlobalOwners.Owners
  unless ← isDefEq (← inferType candidate) old.type do throwError "Global owner carrier changed"
  let candidate ← instantiateMVars candidate
  let after := after.instantiateLevelParams fresh.levelParams candidate.constLevels!
  let child ← getConstInfo ``AspisR1.FJu_Remaining.Holds
  let leaf ← mkConstWithFreshMVarLevels ``AspisR1.FJv_OwnerLeaf.Holds
  unless ← isDefEq (← inferType leaf) child.type do throwError "Global leaf carrier changed"
  let leaf ← instantiateMVars leaf
  let canon := before.replace fun e =>
    if e.isConstOf ``AspisR1.FJu_Remaining.Holds then
      some (leaf.instantiateLevelParams child.levelParams e.constLevels!) else none
  unless ← withTransparency .reducible (isDefEq canon after) do
    throwError "Global owner quantifiers/guards changed beyond replacing Pair-and-Endpoint by Endpoint"
  logInfo "GLOBAL OWNER EXACT: unchanged carriers, quantifiers and guards; Pair-and-Endpoint replaced by the identical Endpoint"
run_meta do
  let old ← getConstInfo ``AspisR1.ARX_Nonvacuity.conditional
  let fresh ← mkConstWithFreshMVarLevels ``AspisR1.FJv_Nonvacuity.conditional
  unless ← isDefEq old.type (← inferType fresh) do throwError "Conditional real-byte fixture statement changed"
  logInfo "NONVACUITY FIXTURE: identical inherited conditional accepted runtime statement"
