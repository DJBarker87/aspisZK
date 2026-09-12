import FSV8V7WholeScriptAlignment
import FSV8V7FiniteUniformBridge

/-!
# Uniform-law transport for a whole bounded script

This is the exact pushforward above `run_compileScript_aligned`.  Its source
law is an explicit uniform finite tape.  It is not a deployed random-oracle or
adversarial-source coupling theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7WholeScriptUniformLaw

open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSFirstFresh
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8V7WholeScriptAlignment FSV8V7FiniteUniformBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

inductive ScriptHalt (A : Type) where
  | returned (value : A)
  | controllerRefused

def currentHalt {A : Type} : Option A -> ScriptHalt A
  | some value => .returned value
  | none => .controllerRefused

/-- `none` keeps all V7 halt kinds not represented by the bounded Script
semantics visible.  The pointwise theorem proves this case cannot occur under
the stated resource bounds. -/
def machineHalt {A : Type} : MachineHalt A -> Option (ScriptHalt A)
  | .returned value => some (.returned value)
  | .oracleAbort .controllerRefused => some .controllerRefused
  | _ => none

def projectMachineRun {A : Type} (run : MachineRun A) :
    Option (ScriptHalt A) × State Bytes Block :=
  (machineHalt run.halt, projectOracleState run.oracle)

def extendFreshTape {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) : Tape :=
  let finite := freshToFin finiteTape
  fun i => if h : i < steps then finite ⟨i, h⟩ else fallback

theorem extendFreshTape_compatible {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (i : Nat) (h : i < steps) :
    extendFreshTape finiteTape fallback i =
      (freshAnswerTapeToList finiteTape).get ⟨i, by simpa using h⟩ := by
  have listEq : freshAnswerTapeToList finiteTape =
      List.ofFn (freshToFin finiteTape) := by
    calc
      freshAnswerTapeToList finiteTape =
          freshAnswerTapeToList (finFreshEquiv steps (freshToFin finiteTape)) :=
        congrArg freshAnswerTapeToList
          (freshToFinEquiv_list steps finiteTape).symm
      _ = List.ofFn (freshToFin finiteTape) :=
        finFreshEquiv_list steps (freshToFin finiteTape)
  simp [extendFreshTape, h, listEq]

theorem aligned_projectOracleState_eq {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs) :
    projectOracleState v7 = fs := by
  cases fs with
  | mk cache next log =>
    unfold projectOracleState
    congr 1
    · funext input
      exact (aligned.cache input).symm
    · exact aligned.freshCalls
    · exact aligned.history.symm

theorem resultAligned_machineHalt {A : Type} (result : Option A)
    (halt : MachineHalt A) (aligned : ResultAligned result halt) :
    machineHalt halt = some (currentHalt result) := by
  cases result with
  | none => simp [ResultAligned] at aligned; simp [aligned, machineHalt, currentHalt]
  | some value =>
    simp [ResultAligned] at aligned
    simp [aligned, machineHalt, currentHalt]

def currentRun {A : Type} {steps n : Nat}
    (fallback : Block) (script : Script Bytes Block A n)
    (finiteTape : FreshAnswerTape Block steps) :
    Option (ScriptHalt A) × State Bytes Block :=
  let source := run (extendFreshTape finiteTape fallback) script
    (FSFirstFresh.empty : State Bytes Block)
  (some (currentHalt source.1), source.2)

/-- Pointwise equality on every finite tape.  In particular the V7 run has no
resource abort or out-of-fuel result under these hypotheses; Script abort is
exactly controller refusal. -/
theorem currentRun_eq_projectMachineRun {A : Type} {steps n : Nat}
    (fallback : Block) (script : Script Bytes Block A n)
    (limits : OracleLimits) (actor : QueryActor)
    (calls : n <= limits.totalCalls) (fresh : n <= limits.freshCalls)
    (fits : n <= steps) (finiteTape : FreshAnswerTape Block steps) :
    currentRun fallback script finiteTape =
      projectMachineRun
        (runMachineFromUniformFreshTape steps limits actor n
          (compileScript script) finiteTape) := by
  let tape := extendFreshTape finiteTape fallback
  have initial : StateAligned tape finiteTape emptyOracle
      (FSFirstFresh.empty : State Bytes Block) :=
    empty_aligned tape finiteTape
      (extendFreshTape_compatible finiteTape fallback)
  have compared := run_compileScript_aligned limits actor script emptyOracle
    (FSFirstFresh.empty : State Bytes Block) initial
    (by simpa [emptyOracle] using calls)
    (by simpa [emptyOracle] using fresh)
    (by simpa [FSFirstFresh.empty] using fits)
  rcases compared with ⟨haltAligned, stateAligned⟩
  unfold currentRun projectMachineRun runMachineFromUniformFreshTape
  change (some (currentHalt (run tape script FSFirstFresh.empty).1),
      (run tape script FSFirstFresh.empty).2) = _
  rw [resultAligned_machineHalt _ _ haltAligned]
  rw [aligned_projectOracleState_eq stateAligned]

noncomputable def currentUniformLaw {A : Type} (steps : Nat)
    (fallback : Block) {n : Nat} (script : Script Bytes Block A n) :
    PMF (Option (ScriptHalt A) × State Bytes Block) :=
  (uniformDigestFreshTape steps).map (currentRun fallback script)

noncomputable def currentFinUniformLaw {A : Type} (steps : Nat)
    (fallback : Block) {n : Nat} (script : Script Bytes Block A n) :
    PMF (Option (ScriptHalt A) × State Bytes Block) :=
  (PMF.uniformOfFintype (Fin steps -> Block)).map
    (fun finite => currentRun fallback script (finFreshEquiv steps finite))

theorem current_fin_uniform_eq_fresh_uniform {A : Type} (steps : Nat)
    (fallback : Block) {n : Nat} (script : Script Bytes Block A n) :
    currentFinUniformLaw steps fallback script =
      currentUniformLaw steps fallback script := by
  unfold currentFinUniformLaw currentUniformLaw uniformDigestFreshTape
  rw [← uniform_finFreshEquiv]
  rw [PMF.map_comp]
  rfl

noncomputable def projectedMachineUniformLaw {A : Type} (steps : Nat)
    (limits : OracleLimits) (actor : QueryActor) {n : Nat}
    (script : Script Bytes Block A n) :
    PMF (Option (ScriptHalt A) × State Bytes Block) :=
  (uniformFreshOracleMachineLaw steps limits actor n
    (compileScript script)).map projectMachineRun

/-- Exact PMF pushforward equality for the explicit uniform finite-tape
experiment.  This consumes the V7 uniform machine law definition and the
pointwise deterministic refinement; it supplies no real-ROM coupling. -/
theorem current_uniform_law_eq_projected_machine {A : Type} (steps : Nat)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    {n : Nat} (script : Script Bytes Block A n)
    (calls : n <= limits.totalCalls) (fresh : n <= limits.freshCalls)
    (fits : n <= steps) :
    currentUniformLaw steps fallback script =
      projectedMachineUniformLaw steps limits actor script := by
  unfold currentUniformLaw projectedMachineUniformLaw
    uniformFreshOracleMachineLaw
  rw [PMF.map_comp]
  congr 1
  funext finiteTape
  exact currentRun_eq_projectMachineRun fallback script limits actor
    calls fresh fits finiteTape

theorem current_fin_uniform_law_eq_projected_machine {A : Type} (steps : Nat)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    {n : Nat} (script : Script Bytes Block A n)
    (calls : n <= limits.totalCalls) (fresh : n <= limits.freshCalls)
    (fits : n <= steps) :
    currentFinUniformLaw steps fallback script =
      projectedMachineUniformLaw steps limits actor script := by
  rw [current_fin_uniform_eq_fresh_uniform]
  exact current_uniform_law_eq_projected_machine steps fallback limits actor
    script calls fresh fits

#print axioms extendFreshTape_compatible
#print axioms currentRun_eq_projectMachineRun
#print axioms current_uniform_law_eq_projected_machine
#print axioms current_fin_uniform_law_eq_projected_machine

end AspisV8Completion.FSV8V7WholeScriptUniformLaw
