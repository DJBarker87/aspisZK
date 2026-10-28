import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayStep
set_option autoImplicit false

theorem read {T : Type} (v : Slice T) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok v.val[i.val] := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]

theorem write {T : Type} {N : Usize} (v : Array T N) (i : Usize) (x : T)
    (h : i.val < N.val) : Array.update v i x = ok (v.set i x) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq,List.getElem?_eq_getElem (by simpa [v.property] using h)]
  rfl

theorem increment (i N : Usize) (h : i.val < N.val) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have := N.hSize
  omega

theorem done {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize)
    (h : N.val ≤ i.val) :
    PV_CBL_ArrayKernel.array_reference_loop.body v out i = ok (.done out) := by
  have hn : ¬i<N := by change ¬i.val<N.val; omega
  simp only [PV_CBL_ArrayKernel.array_reference_loop.body,hn,if_false]

theorem continuing {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize)
    (h : i.val<N.val) (hv : i.val<v.val.length) :
    PV_CBL_ArrayKernel.array_reference_loop.body v out i =
      ok (.cont (out.set i v.val[i.val],Usize.wrapping_add i 1#usize)) := by
  have hn : i<N := h
  simp only [PV_CBL_ArrayKernel.array_reference_loop.body,hn,if_true,read v i hv,
    write out i _ h,lift,bind_tc_ok]
#print axioms read
#print axioms write
#print axioms increment
#print axioms done
#print axioms continuing
end R1Z.PV_CBL_ArrayStep
