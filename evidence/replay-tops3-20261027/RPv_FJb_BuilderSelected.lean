import RPv_FJb_BuilderStable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_BuilderSelected
open Aeneas Aeneas.Std Result
/-- Every selected native constructor cell is the result of its SAME stable
callback at that index. No independently chosen output array is a premise. -/
theorem value {T C : Type} (N : Usize) (copy : core.marker.Copy T)
    (f : core.ops.function.FnMut C Usize T) (dummy : T) (c : C)
    (stable : ∀ i : Usize,i.val < N.val → ∃ x,f.call_mut c i=ok (x,c))
    (out : Array T N)
    (run : FIq_Native.array_from_fn_copy N copy f dummy c=ok out) :
    ∀ (i : Usize) (hi : i.val < N.val),
      f.call_mut c i=ok (out.val[i.val]'(by simpa only [out.property] using hi),c) := by
  let index (i : Fin N.val) : Usize := Usize.ofNatCore i.val (lt_trans i.isLt N.hBounds)
  have hs : ∀ i : Fin N.val,∃ x,f.call_mut c (index i)=ok (x,c) := by
    intro i
    apply stable
    simpa [index] using i.isLt
  choose values hvalues using hs
  let val (n : Nat) := if h : n < N.val then values ⟨n,h⟩ else dummy
  have hv : ∀ i : Usize,i.val < N.val → f.call_mut c i=ok (val i.val,c) := by
    intro i hi
    have he : index ⟨i.val,hi⟩=i := by apply UScalar.eq_of_val_eq;simp [index]
    simpa only [he,val,dif_pos hi] using hvalues ⟨i.val,hi⟩
  obtain ⟨old,hold,hcells⟩ := AspisR1SelectedMaskProbe.array_from_fn_copy_stable
    N copy f dummy c val hv
  have hn := FJb_BuilderStable.transport N copy f dummy c val hv out run
  have he : old=out := Result.ok.inj (hold.symm.trans hn)
  subst old
  intro i hi
  rw [hcells i.val hi]
  exact hv i hi
#print axioms value
end AspisR1.FJb_BuilderSelected
end
