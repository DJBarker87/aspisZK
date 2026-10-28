import R1Z.PV_W_Callbacks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeHash38
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

def reify (hash : Slice (Slice U8) → Result (Array U8 32#usize)) : PV_W_Callbacks.Hash :=
  fun parts => PV_W_ReachedEffects.invoke "Digest32.hash" (fun _ => hash parts)

/-- Preserve the exact source callback on erasure, while leaving each real
hash invocation visible to the runtime helper interpretation. -/
theorem source (ops : ExternalFuns) (hash : Slice (Slice U8) → Result (Array U8 32#usize)) :
    PV_W_Callbacks.sourceHash ops (reify hash)=hash := by
  funext parts
  exact PV_W_ReachedEffects.erase_invoke ops "Digest32.hash" (fun _ => hash parts)

#print axioms source
end R1Z.PV_RunJoin_RuntimeHash38
