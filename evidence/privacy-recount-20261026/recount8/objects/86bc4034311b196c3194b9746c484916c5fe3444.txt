import R1Z.PV_W_R_Entry
import R1Z.PV_RunJoin_PreparedCaller32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReachedSource33
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ExternalTypes]

/-- A value-only hash lift used exclusively for the source-erasure equation.
It asserts no native absence of oracle, TLS or allocation effects. -/
def liftHash (hash : Hash) : PV_W_Callbacks.Hash := fun a =>
  PV_W_ReachedEffects.invoke "runjoin.associated.hash" (fun _ => hash a)

theorem sourceHash (ops : ExternalFuns) (hash : Hash) :
    PV_W_Callbacks.sourceHash ops (liftHash hash) = hash := by
  funext a
  exact PV_W_ReachedEffects.erase_invoke ops _ _

/-- The recursive pv-world body erases to the actual emitted caller at all
arguments, including both Result layers, source failure and divergence. -/
theorem entry (ops : ExternalFuns) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (secret : Secret) (store : Store) :
    PV_W_ReachedEffects.erase ops
      (PV_W_R_Entry.program pub compiled .S2 (liftHash hash) secret store) =
    @prover.prove_masked_attempt _ ops pub compiled .S2 hash secret store := by
  rw [PV_W_R_Entry.erase_program,sourceHash]

variable {N C : Type}
/-- The same complete Result at the canonical associated caller inputs.
Canonical preparation supplies these inputs through PreparedCaller32; no
alternative payload or semantic projection is substituted here. This is a
source-erasure statement, not the still-missing security-model simulation. -/
theorem associated (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    let d := PV_RunJoin_NativeSelectedInputs.inputs base ops hash i
    ∀ secret, PV_W_ReachedEffects.erase (d.ops s)
      (PV_W_R_Entry.program (d.pub s) (d.compiled s) .S2
        (liftHash (d.hash s)) secret s.ledger) =
      PV_RunJoin_PureSourceLift.native d s secret := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  dsimp only
  intro secret
  exact entry _ _ _ _ _ _

#print axioms sourceHash
#print axioms entry
#print axioms associated
end R1Z.PV_RunJoin_ReachedSource33
