import FIx_Builder
import ArrayFromFnCopyStable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_BuilderStable
open Aeneas Aeneas.Std Result
/-- Relate the installed ordered constructor to the retained extracted loop
when its actual callback has been proved stable on every selected index. -/
theorem transport {T C : Type} (N : Usize) (copy : core.marker.Copy T)
    (f : core.ops.function.FnMut C Usize T) (dummy : T) (c : C)
    (value : Nat → T)
    (stable : ∀ i : Usize,i.val < N.val → f.call_mut c i=ok (value i.val,c))
    (out : Array T N)
    (run : FIq_Native.array_from_fn_copy N copy f dummy c=ok out) :
    AspisR1SelectedMaskProbe.array_from_fn_copy N copy f dummy c=ok out := by
  obtain ⟨old,hold,hvalue⟩ := AspisR1SelectedMaskProbe.array_from_fn_copy_stable
    N copy f dummy c value stable
  have hn := FIx_Builder.fromFn N f (fun _=>True) id value c out
    (by
      intro i hi x last call
      rw [stable i hi] at call
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj call)
      exact ⟨True.intro,rfl,rfl⟩) run
  have vals : out.val=List.ofFn (fun i : Fin N.val=>value i.val) := by
    simpa only [List.map_id_fun] using hn.2
  have eq : old=out := by
    apply Subtype.ext
    rw [vals]
    apply List.ext_getElem
    · simp only [old.property,List.length_ofFn]
    · intro i hi hj
      simpa only [List.getElem_ofFn] using hvalue i (by simpa only [old.property] using hi)
  exact eq ▸ hold
theorem total {T C : Type} (N : Usize) (copy : core.marker.Copy T)
    (f : core.ops.function.FnMut C Usize T) (dummy : T) (c : C)
    (stable : ∀ i : Usize,i.val < N.val → ∃ x,f.call_mut c i=ok (x,c))
    (out : Array T N)
    (run : FIq_Native.array_from_fn_copy N copy f dummy c=ok out) :
    AspisR1SelectedMaskProbe.array_from_fn_copy N copy f dummy c=ok out := by
  let index (i : Fin N.val) : Usize := Usize.ofNatCore i.val (lt_trans i.isLt N.hBounds)
  have hs : ∀ i : Fin N.val,∃ x,f.call_mut c (index i)=ok (x,c) := by
    intro i
    apply stable
    simpa only [index,UScalar.ofNatCore_val_eq] using i.isLt
  choose values hvalues using hs
  let value (n : Nat) := if h : n < N.val then values ⟨n,h⟩ else dummy
  apply transport N copy f dummy c value _ out run
  intro i hi
  have he : index ⟨i.val,hi⟩=i := by
    apply UScalar.eq_of_val_eq
    simp only [index,UScalar.ofNatCore_val_eq]
  simpa only [he,value,dif_pos hi] using hvalues ⟨i.val,hi⟩
#print axioms transport
#print axioms total
end AspisR1.FJb_BuilderStable
end
