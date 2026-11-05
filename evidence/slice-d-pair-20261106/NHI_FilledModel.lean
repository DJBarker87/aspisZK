import NHI_Scalar
set_option autoImplicit false
noncomputable section
namespace NHI_FilledModel
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NP6_StdModel

def vector {T : Type} (n : Usize) (value : T) : alloc.vec.Vec T :=
 ⟨List.replicate n.val value,by simp;scalar_tac⟩

def result {T : Type} (reservation : Reservation) (n : Usize) (value : T) :
 Result (core.result.Result (alloc.vec.Vec T) FIo_Native.aspis_core.r0.Error) :=
 match reservation with
 | .Err _ => ok (.Err .Allocation)
 | .Ok () => ok (.Ok (vector n value))

/-- Retained allocator interpretation is explicit and covers both reserve arms.
The clone law is a value law, never a successful allocation premise. -/
theorem contents (reservation : Reservation) {T : Type}
 (copy : core.marker.Copy T) (n : Usize) (value : T)
 (cloned : copy.cloneInst.clone value=ok value) :
 letI := FIo_Install.allocation reservation
 FIo_Native.aspis_core.r0.heap.filled copy n value=result reservation n value := by
 cases reservation with
 | Err e => rfl
 | Ok u =>
  cases u
  simp only [FIo_Native.aspis_core.r0.heap.filled,FIo_Install.allocation,
   FIo_Native.alloc.vec.Vec.try_reserve_exact,FIo_Native.Allocation.reserve,alloc.vec.Vec.new,
   FIo_Native.core.result.Result.map_err,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch]
  simp [alloc.vec.Vec.resize,List.resize,cloned,result,vector]

theorem qm (reservation : Reservation) (n : Usize) (value : NQ) :
 letI := FIo_Install.allocation reservation
 FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy n value=
 result reservation n value := contents reservation _ n value (by rfl)

theorem length {T : Type} (n : Usize) (value : T) :
 (vector n value).val.length=n.val := List.length_replicate

theorem selected {T : Type} (n : Usize) (value : T) (i : Nat) (hi : i<n.val) :
 (vector n value).val[i]?=some value := by simp [vector,hi]

theorem canonical (n : Usize) (value : NQ) (hc : canonQ value) :
 ∀ x∈(vector n value).val,canonQ x := by
 intro x hx
 simp only [vector,List.mem_replicate] at hx
 exact hx.2 ▸ hc

#print axioms contents
#print axioms qm
#print axioms length
#print axioms selected
#print axioms canonical
end NHI_FilledModel
end
