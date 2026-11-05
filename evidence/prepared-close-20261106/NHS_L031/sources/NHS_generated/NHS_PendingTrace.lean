import NHS_PendingStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PendingTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativePendingBody
/-- The physical constructor's local windows are threaded on one raw allocation.
No full loop result or independently chosen successful output is assumed. -/
inductive Cuts (weights : Slice aspis_core.field.QM31) :
 alloc.vec.Vec Row → Usize → alloc.vec.Vec Row → Prop where
 | done (raw : alloc.vec.Vec Row) (index : Usize) (last : index.val=64) : Cuts weights raw index raw
 | step (raw after out : alloc.vec.Vec Row) (index next : Usize) (w : aspis_core.field.QM31)
   (active : index.val<64) (size : raw.val.length=64)
   (read : Slice.index_usize weights index=ok w)
   (windows : NHS_PendingStep.Windows raw after index next w)
   (rest : Cuts weights after next out) : Cuts weights raw index out

theorem source (weights : Slice aspis_core.field.QM31)
 (raw out : alloc.vec.Vec Row) (index : Usize) (size : weights.val.length=64)
 (cuts : Cuts weights raw index out) : run weights raw index=ok out := by
 induction cuts with
 | done raw index last =>
   have inactive : ¬index<Slice.len weights := by change ¬index.val<weights.val.length;omega
   unfold run
   rw [Aeneas.Std.loop.eq_def]
   simp only [body,if_neg inactive,bind_tc_ok]
 | step raw after out index next w active rawsize read windows rest ih =>
   have localStep := NHS_PendingStep.source weights raw after index next w size rawsize active read windows
   unfold run
   rw [Aeneas.Std.loop.eq_def,localStep,bind_tc_ok]
   exact ih
#print axioms source
end AspisR1.NHS_PendingTrace
