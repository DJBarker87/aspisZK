import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditData
import R1Z.PV_RunJoin_ReachedSource33
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualAudit34
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverRw19AuditValue ProverRw19AuditData
variable [ExternalTypes]

/-- The guards of the entire emitted attempt force the canonical audit.
Every helper result is arbitrary here; no successful-body or model equation
is assumed. This discharges only the audit-value part of V163. -/
theorem entry_good (ops : ExternalFuns) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (secret : Secret) (store : Store) :
    Good (@prover.prove_masked_attempt _ ops pub compiled .S2 hash secret store) := by
  letI : ExternalFuns := ops
  unfold prover.prove_masked_attempt
  repeat' first
    | exact ProverRw19AuditSource.body _ _ _ _ _ _ _ _ _
    | exact residual _ _
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

/-- Complete status comparison for the audit: source fail/divergence and
inner Err are kept. The byte status here is the source observation, so this
is explicitly NOT the missing independent security-model byte equation. -/
theorem complete_audit (ops : ExternalFuns) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (secret : Secret) (store : Store) :
    let actual := @prover.prove_masked_attempt _ ops pub compiled .S2 hash secret store
    ProverRwBodyDataCriterion.data actual = attachAudit
      (PV_RW_DataProduct.observe PV_RW_DataProduct.first (ProverRwBodyDataCriterion.data actual)) := by
  exact data_of_bytes _ _ (entry_good ops pub compiled hash secret store) rfl

local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N C : Type}

/-- Audit/status comparison at the original canonical-associated caller
coordinates, with no replacement compilation or source-result hypothesis. -/
theorem associated (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    ∀ secret,
      ProverRwBodyDataCriterion.data
        (PV_RunJoin_PureSourceLift.native (PV_RunJoin_NativeSelectedInputs.inputs base ops hash i) s secret) =
      attachAudit (PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (ProverRwBodyDataCriterion.data
          (PV_RunJoin_PureSourceLift.native (PV_RunJoin_NativeSelectedInputs.inputs base ops hash i) s secret))) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  intro secret
  exact complete_audit _ _ _ _ _ _

#print axioms entry_good
#print axioms complete_audit
#print axioms associated
end R1Z.PV_RunJoin_ActualAudit34
