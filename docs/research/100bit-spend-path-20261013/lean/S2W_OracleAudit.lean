import S2Z_Oracle

/-! A statement audit for the universal Required14 oracle field. These are
interface countermodels, never claims about a native accepted transaction.
Successful-return interpretation and finite observed calls do not entail
unrestricted returning behavior on inputs outside that observation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W.OracleAudit
open Aeneas Aeneas.Std Result
open AspisR1.S2Z.Oracle
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Preserve the backend everywhere except one unobserved input. -/
def mask (backend : Parts → Result Digest) (blocked parts : Parts) : Result Digest :=
  if parts = blocked then .div else backend parts

/-- The existing runtime successful-return premise survives this change. -/
theorem mask_runtime (backend : Parts → Result Digest) (sha256 : Bytes → State)
    (runtime : RuntimeSyscall backend sha256) (blocked : Parts) :
    RuntimeSyscall (mask backend blocked) sha256 := by
  intro parts digest returned
  unfold mask at returned
  split at returned
  · cases returned
  · exact runtime parts digest returned

/-- Every supplied observed call is identical, including errors/divergence.
This is input/output preservation only, without a native execution assertion. -/
theorem mask_observed (backend : Parts → Result Digest) (blocked : Parts)
    (observed : List Parts) (unobserved : blocked ∉ observed) :
    ∀ parts, parts ∈ observed → mask backend blocked parts = backend parts := by
  intro parts member
  have different : parts ≠ blocked := by
    intro same
    subst parts
    exact unobserved member
  simp only [mask,if_neg different]

/-- Even with explicit NativeBinding and the unchanged RuntimeSyscall law,
Required14's unrestricted oracle conclusion fails at the masked input.
P1 can remain any fixed realization: it cannot imply backend termination. -/
theorem bound_runtime_not_total (ops : AdapterRw.Ops)
    (backend : Parts → Result Digest) (sha256 H : Bytes → State)
    (runtime : RuntimeSyscall backend sha256) (blocked : Parts) :
    let changed := {ops with op43 := fun _ parts => mask backend blocked parts}
    NativeBinding changed (mask backend blocked) ∧
    RuntimeSyscall (mask backend blocked) sha256 ∧
    ¬ (∀ parts, (leadDigest changed).digest () parts =
      ok (MultiproofConePhysicalTransport.rawOracle H parts)) := by
  dsimp only
  refine ⟨fun _ _ => rfl, mask_runtime backend sha256 runtime blocked, ?_⟩
  intro total
  have impossible := total blocked
  change mask backend blocked blocked = _ at impossible
  simp only [mask,if_pos rfl] at impossible
  cases impossible

#print axioms mask_runtime
#print axioms mask_observed
#print axioms bound_runtime_not_total
end AspisR1.S2W.OracleAudit
end
