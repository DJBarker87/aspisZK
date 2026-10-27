import FJj_QMSlice
import FIo_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_Filled
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)

theorem contents (r : NP6_StdModel.Reservation) (n : Usize) :
    @FIo_Native.aspis_core.r0.heap.filled (FIo_Install.allocation r) NQ
      FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy n FIo_Native.aspis_core.field.QM31.ZERO=
    match r with
    | .Err _=>ok (.Err .Allocation)
    | .Ok ()=>ok (.Ok (⟨List.replicate n.val FIo_Native.aspis_core.field.QM31.ZERO,
        by simp;scalar_tac⟩ : alloc.vec.Vec NQ)) := by
  cases r with
  | Err e=>rfl
  | Ok u=>
    cases u
    simp only [FIo_Native.aspis_core.r0.heap.filled,FIo_Install.allocation,
      FIo_Native.alloc.vec.Vec.try_reserve_exact,alloc.vec.Vec.new,
      FIo_Native.core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
    simp [alloc.vec.Vec.resize,List.resize,
      FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy,
      FIo_Native.aspis_core.field.QM31.Insts.CoreCloneClone.clone]

theorem canonical (r : NP6_StdModel.Reservation) (n : Usize) (v : alloc.vec.Vec NQ)
    (run : @FIo_Native.aspis_core.r0.heap.filled (FIo_Install.allocation r) NQ
      FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy n FIo_Native.aspis_core.field.QM31.ZERO=ok (.Ok v)) :
    FJj_QMSlice.canon (alloc.vec.Vec.deref v) := by
  rw [contents] at run
  cases r with
  | Err e=>cases run
  | Ok u=>
    cases u
    cases core.result.Result.Ok.inj (Result.ok.inj run)
    intro x hx
    simp only [alloc.vec.Vec.deref,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    simp [FIo_QMValues.Canon,FIo_CMValues.Canon,FIo_Native.aspis_core.field.QM31.ZERO]

#print axioms canonical
#print axioms contents
end AspisR1.FJm_Filled
end
