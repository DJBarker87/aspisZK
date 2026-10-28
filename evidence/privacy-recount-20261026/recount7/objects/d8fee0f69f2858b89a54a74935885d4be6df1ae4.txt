import R1Z.PV_AL_MoveFacts
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_MoveLast
set_option autoImplicit false

theorem remove_last {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    PV_AL_RemoveModel.remove Global v (Usize.wrapping_sub (alloc.vec.Vec.len v) 1#usize)=
      ok (v.val[v.val.length-1]'(PV_AL_MoveFacts.last_bound v h),
        (PV_CBL_VectorPopSpec.pop v).2) := by
  simp only [PV_AL_RemoveModel.remove,PV_AL_MoveFacts.last_value v h,
    List.getElem?_eq_getElem (PV_AL_MoveFacts.last_bound v h)]
  apply congrArg Result.ok
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp only [PV_AL_MoveFacts.empty_suffix v.val h,List.append_nil,
      PV_CBL_VectorPopSpec.pop,List.dropLast_eq_take]

theorem nonempty {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    PV_AL_RemoveModel.pop_move_reference v=
      ok (some (v.val[v.val.length-1]'(PV_AL_MoveFacts.last_bound v h)),
        (PV_CBL_VectorPopSpec.pop v).2) := by
  have hn : alloc.vec.Vec.len v ≠ 0#usize := by
    intro hz
    have hl := congrArg (fun n : Usize => n.val) hz
    change v.val.length=0 at hl
    exact h (List.eq_nil_of_length_eq_zero hl)
  simp only [PV_AL_RemoveModel.pop_move_reference,if_neg hn,lift,bind_tc_ok,remove_last v h]
  rfl

theorem source {T : Type} (v : alloc.vec.Vec T) :
    PV_AL_RemoveModel.pop_move_reference v=PV_CBL_VectorPopSpec.reference v := by
  by_cases h : v.val=[]
  · have hv : v=alloc.vec.Vec.new T := Subtype.ext h
    subst v
    rfl
  · rw [nonempty v h]
    unfold PV_CBL_VectorPopSpec.reference
    apply congrArg Result.ok
    apply Prod.ext
    · exact (PV_AL_PopLast.last v.val h).symm
    · rfl

#print axioms remove_last
#print axioms nonempty
#print axioms source
end R1Z.PV_AL_MoveLast
