import NHW_QueryIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_QueryObstruction
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
abbrev E := aspis_core.field.wide_exact.WideExact
/-- The line implementation is replaced by NFS even when the input callback
is divergent. These are legitimate abstract Configuration.query values. -/
def divergent (ops : Ops) : Ops := {ops with op16:=fun _ _ _ => div}
def returning (ops : Ops) : Ops := {ops with op16:=fun alpha _ _ => ok alpha}
theorem erased_difference (ops : Ops) :
 NFS_QueryOps.installed (divergent ops)=NFS_QueryOps.installed (returning ops) := rfl
/-- The adopted leaves installation preserves a genuine primitive difference. -/
theorem retained_difference (ops : Ops) (alpha : E) :
 Tx1Q_QueryBridge.leaves (divergent ops) ≠ Tx1Q_QueryBridge.leaves (returning ops) := by
 intro same
 have h := congrArg (fun d : Ops =>
   d.op16 alpha (Array.repeat 4#usize alpha) (Array.repeat 5#usize 0#u32)) same
 change (div : Result E)=ok alpha at h
 cases h
/-- Refutes the requested unrestricted identification without choosing or
assuming a successful query/transaction result. -/
theorem not_universal (ops : Ops) (alpha : E) :
 ¬ (∀ query : Ops, Tx1Q_QueryBridge.leaves query=NFS_QueryOps.installed query) := by
 intro all
 apply retained_difference ops alpha
 exact (all (divergent ops)).trans ((erased_difference ops).trans (all (returning ops)).symm)
#print axioms erased_difference
#print axioms retained_difference
#print axioms not_universal
end AspisR1.NHW_QueryObstruction
