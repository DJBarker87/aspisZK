import Port21PROJECTION_Core
import OraclePortRuntimeBindingC7

/-! A soundness-only projection interface for the actual stored-run extractor
and its memoized probability law. Rejected terminal values need not agree;
all issued oracle calls still agree. No concrete native Sim is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port21PROJECTION_Experiment
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
open Port21PROJECTION_Core

abbrev NativeRuntime (Private : Type) := Program Bytes State (Option RunView × Private)

/-- Terminal simulation obligation, checked only after the ordered causal
steps: a native accepted stored run keeps exactly the extractor's full view.
No requirement on rejected public outputs or private allocation/cleanup state.
This is NOT a native helper contract or an implementation of this relation. -/
def AcceptedLeaf {Private : Type} (n : Option RunView × Private) (m : Option RunView) : Prop :=
  ∀ run, n.1 = some run → run.2.2 = true → m = some run

def nativeMass {Private : Type} (v : View Bytes State (Option RunView × Private)) : ℚ :=
  OraclePortRuntimeBindingC7.runtimeMass (v.1,v.2.1)

theorem nonnegative (log : List (Bytes × State)) (m : Option RunView) :
    0 ≤ OraclePortRuntimeBindingC7.runtimeMass (log,m) := by
  cases m with
  | none => exact le_refl _
  | some run => exact OraclePortRuntimeBindingC7.failure_nonnegative _

/-- Exact private-coin extraction-failure event; no replacement extractor,
fresh-oracle experiment, or accepted-output-only observation is introduced. -/
theorem accepted_event {Private : Type} (n : Option RunView × Private) (m : Option RunView)
    (leaf : AcceptedLeaf n m) (run : RunView)
    (present : n.1 = some run) (accepted : run.2.2 = true)
    (coins : GSConcreteByteDecoderBank.RawCoins)
    (failed : RawRecordedPublicSpendExtractorBin.extract (view run) coins = none) :
    m = some run ∧ RawRecordedPublicSpendExtractorBin.extract (view run) coins = none :=
  ⟨leaf run present accepted,failed⟩

theorem leaf_mass {Private : Type} (log : List (Bytes × State))
    (n : Option RunView × Private) (m : Option RunView) (leaf : AcceptedLeaf n m) :
    nativeMass (log,n) ≤ OraclePortRuntimeBindingC7.runtimeMass (log,m) := by
  cases present : n.1 with
  | none =>
    simpa only [nativeMass,OraclePortRuntimeBindingC7.runtimeMass,present] using nonnegative log m
  | some run =>
    by_cases accepted : run.2.2 = true
    · rw [leaf run present accepted]
      simp only [nativeMass,OraclePortRuntimeBindingC7.runtimeMass,present,le_refl]
    · have zero : failureMass (view run) = 0 := by
        unfold failureMass
        simp only [view] at *
        simp [accepted,indicator,mean_const]
      simpa only [nativeMass,OraclePortRuntimeBindingC7.runtimeMass,present,zero] using nonnegative log m

/-- The event upper bound holds under the existing lazy shared-oracle law.
Sim is a step relation for every answer branch, not an assumed mass inequality.
Private terminal state can be forgotten; the full accepted extractor view cannot. -/
theorem failure_transport {Private : Type} (native : NativeRuntime Private)
    (model : OraclePortRuntimeBindingC7.Runtime) (steps : Sim AcceptedLeaf native model) :
    lazyMean native emptyTable nativeMass ≤ OraclePortRuntimeBindingC7.deployedFailure model :=
  mass_le steps nativeMass OraclePortRuntimeBindingC7.runtimeMass leaf_mass

/-- All-outcome query accounting includes the complete prefix before any
rejection/abort terminal, irrespective of AcceptedLeaf's vacuous reject case. -/
theorem all_outcome_queries {Private : Type} (native : NativeRuntime Private)
    (model : OraclePortRuntimeBindingC7.Runtime) (steps : Sim AcceptedLeaf native model)
    (H : Bytes → State) :
    (eval H native).1.length = (eval H model).1.length ∧
    firstReads emptyTable (eval H native).1 = firstReads emptyTable (eval H model).1 :=
  ⟨charge steps H List.length,charge steps H (firstReads emptyTable)⟩

/-- Weaker ROOT interface: only accepted extractor views match. Rejected
runtime logs may differ. This is valid only at the complete experiment root,
not as an arbitrary adaptive subroutine substitution. The hypothesis is shown
in full; constructing it from actual source remains a separate obligation. -/
theorem accepted_mass_transport {Private : Type} (native : NativeRuntime Private)
    (model : OraclePortRuntimeBindingC7.Runtime)
    (matched : ∀ H : Bytes → State, AcceptedLeaf (eval H native).2 (eval H model).2) :
    lazyMean native emptyTable nativeMass ≤ OraclePortRuntimeBindingC7.deployedFailure model := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  exact leaf_mass (eval H native).1 (eval H native).2 (eval H model).2 (matched H)

/-- The ROOT acceptance interface above does not imply a query bound.
The separate ALL-OUTCOME source charge obligation is deliberately explicit.
No error/abort prefix is conditioned away, and Q is not an accepted-run cost. -/
theorem soundness_and_query_transport {Private : Type} (native : NativeRuntime Private)
    (model : OraclePortRuntimeBindingC7.Runtime) (Q : Nat) (ε : ℚ)
    (matched : ∀ H : Bytes → State, AcceptedLeaf (eval H native).2 (eval H model).2)
    (accounted : ∀ H : Bytes → State, (eval H native).1.length ≤ Q)
    (bound : OraclePortRuntimeBindingC7.deployedFailure model ≤ ε) :
    lazyMean native emptyTable nativeMass ≤ ε ∧
      ∀ H : Bytes → State, (eval H native).1.length ≤ Q :=
  ⟨(accepted_mass_transport native model matched).trans bound,accounted⟩

#print axioms accepted_mass_transport
#print axioms soundness_and_query_transport
#print axioms nonnegative
#print axioms accepted_event
#print axioms leaf_mass
#print axioms failure_transport
#print axioms all_outcome_queries
end AspisR1.Port21PROJECTION_Experiment
end
