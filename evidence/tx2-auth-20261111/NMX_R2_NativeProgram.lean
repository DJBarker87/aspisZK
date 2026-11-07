import NMX_R2_NativeCommands
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeProgram
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Full source execution inclusion, derived from the concrete command laws.
No free Handler/Ops or child-success premise enters this induction. -/
theorem member (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (env : RSL.Env) (term : Program Auth) :
 NMX_R2_Semantics.denote owners ln rn term env
  (NMX_R2_NativeExecution.run owners alloc failure ln rn env term) := by
 induction term with
 | ret value => rfl
 | reject error => rfl
 | stop cause => cases cause <;> rfl
 | @step A cmd next ih =>
   exact NMX_R2_Observation.rust_sound
    (NMX_R2_NativeExecution.command owners alloc failure ln rn env cmd)
    (fun reply => NMX_R2_NativeExecution.run owners alloc failure ln rn env (next reply))
    (NMX_R2_Semantics.command owners ln rn cmd)
    (fun reply => NMX_R2_Semantics.denote owners ln rn (next reply)) env
    (NMX_R2_NativeCommands.member owners alloc failure ln rn env cmd) ih
#print axioms member
end NMX_R2_NativeProgram
end
