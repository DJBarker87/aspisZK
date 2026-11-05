import NHI_FilledExtracted
import NHI_FilledModel
set_option autoImplicit false
noncomputable section
namespace NHI_FilledBridge
open Aeneas Aeneas.Std Result AspisR1
open NP6_StdModel
abbrev Words := Array U32 4#usize

theorem clone (value : Words) :
 core.array.CloneArray.clone core.clone.CloneU32 value=ok value := by
 obtain ⟨out,run,same⟩ := WP.spec_imp_exists
  (Array.clone_spec (s:=value) (clone:=core.clone.CloneU32.clone) (by intro x hx;rfl))
 subst out
 exact run

theorem reference (reservation : Reservation) (n : Usize) (value : Words) :
 letI := FIo_Install.allocation reservation
 NHI_FilledRef.filled_ref n value=
 match reservation with
 | .Err _ => ok (.Err NHI_FilledRef.Error.Allocation)
 | .Ok () => ok (.Ok (NHI_FilledModel.vector n value)) := by
 cases reservation with
 | Err e => rfl
 | Ok u =>
  cases u
  simp only [NHI_FilledRef.filled_ref,NHI_FilledRef.alloc.vec.Vec.try_reserve_exact,
   FIo_Native.alloc.vec.Vec.try_reserve_exact,FIo_Install.allocation,FIo_Native.Allocation.reserve,
   alloc.vec.Vec.new,NHI_FilledRef.core.result.Result.map_err,
   FIo_Native.core.result.Result.map_err,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch]
  simp [alloc.vec.Vec.resize,List.resize,clone,NHI_FilledModel.vector]

#print axioms clone
#print axioms reference
end NHI_FilledBridge
end
