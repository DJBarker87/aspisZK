import CuSavingsProfilingResources
/-! Candidate 2: source dispatcher substitution plus the two exact adapter
logging blocks. The source factorization/inverse audit and fixed callback SDK
binding are recorded in profiling-source-audit/source-audit.json. The runtime
boundary is sufficient REFERENCE resources and returning diagnostic syscalls;
resource exhaustion is not projected into successful verification. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsProfilingCandidate2
open Aeneas Aeneas.Std Result AspisR1Profiling CuSavingsProfilingProjection

structure Hooks where
  observer : Phase → Result Unit
  stage1CheckpointWritten : Result Unit
  stage2Begin : Result Unit

def stage1Events : List Diagnostic :=
  [.message "r1:pool-adapter-stage1-checkpoint-written",.computeUnits]
def stage2Events : List Diagnostic :=
  [.message "r1:pool-adapter-stage2-begin",.computeUnits]

def projectDiagnostics (_events : List Diagnostic) : Result Unit := .ok ()

/-- Concrete callback return and exact diagnostic effect list before projection.
The standard SDK boundary supplies this semantics only for returning executions
with sufficient reference resources, not for allocation or syscall failure. -/
def programCallback (phase : Phase) : Result (Unit × List Diagnostic) :=
  .ok ((),fixedEvents phase)

def projectedProgramCallback (phase : Phase) : Result Unit := do
  let (value,_diagnostics) ← programCallback phase
  .ok value

theorem program_callback_binding (phase : Phase) :
    projectedProgramCallback phase = projectedCallback phase := rfl

def referenceHooks : Hooks where
  observer := dispatcher (some projectedProgramCallback)
  stage1CheckpointWritten := projectDiagnostics stage1Events
  stage2Begin := projectDiagnostics stage2Events

def optimizedHooks : Hooks where
  observer := dispatcher none
  stage1CheckpointWritten := .ok ()
  stage2Begin := .ok ()

theorem hooks_eq : referenceHooks = optimizedHooks := rfl

/-- All exact source call sites and adapter blocks can be replaced together.
`context` is the unchanged source closure factored over its sole observer and
these two diagnostic statements. It may return complete application state,
checkpoint/settlement results, ordered cryptographic traces, errors, or
nontermination; none is required to succeed. -/
theorem complete_source_context_eq {A : Type} (context : Hooks → Result A) :
    context referenceHooks = context optimizedHooks := rfl

theorem all_observations_eq {A Observation : Type} (context : Hooks → Result A)
    (observe : Result A → Observation) :
    observe (context referenceHooks) = observe (context optimizedHooks) := rfl

theorem transfer_contract {A : Type} (context : Hooks → Result A)
    (contract : Result A → Prop) (reference : contract (context referenceHooks)) :
    contract (context optimizedHooks) := reference

/-- Resource statement is separate from semantic equivalence. The actual
formatter allocation trace must fit together with the future reference budget;
its requests, including growth allocations, are not replaced by message sizes. -/
theorem reference_resources_admitted (sizes : List Nat) (free future : Nat)
    (budget : sizes.sum+future ≤ free) :
    CuSavingsProfilingResources.privateAllocations free sizes = .ok (free-sizes.sum) ∧
    future ≤ free-sizes.sum ∧ free-sizes.sum ≤ free := by
  obtain ⟨hrun,hremaining⟩ := CuSavingsProfilingResources.private_allocations_admitted sizes free future budget
  exact ⟨hrun,hremaining,Nat.sub_le _ _⟩

#print axioms program_callback_binding
#print axioms hooks_eq
#print axioms complete_source_context_eq
#print axioms all_observations_eq
#print axioms transfer_contract
#print axioms reference_resources_admitted
#print axioms application_trace_preserved
end AspisR1.CuSavingsProfilingCandidate2
