import AspisR1CanonicalStd.Funs
import AspisR1CanonicalDots.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsAll
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots

theorem source_true {T : Type} (inst : core.ops.function.FnMut Unit T Bool)
    (slice : Slice T) (hcall : ∀ value∈slice.val,inst.call_mut () value=.ok (true,()))
    (fuel i : Nat) (hi : i≤slice.val.length) (hf : slice.val.length-i=fuel) :
    AspisR1CanonicalStd.all_loop inst ⟨slice,i⟩ () =
      .ok (true,⟨slice,slice.val.length⟩) := by
  induction fuel generalizing i with
  | zero =>
      have he : i=slice.val.length := by omega
      cases he
      unfold AspisR1CanonicalStd.all_loop
      rw [loop]
      simp [AspisR1CanonicalStd.all_loop.body,
        core.slice.iter.IteratorSliceIter.next,Slice.len]
  | succ fuel ih =>
      have hlt : i<slice.val.length := by omega
      have hmem : slice.val[i]'hlt∈slice.val := List.getElem_mem hlt
      have hc := hcall _ hmem
      unfold AspisR1CanonicalStd.all_loop
      rw [loop]
      have hn : core.slice.iter.IteratorSliceIter.next (⟨slice,i⟩ : core.slice.iter.Iter T)=
          .ok (some (slice.val[i]'hlt),⟨slice,i+1⟩) := by
        unfold core.slice.iter.IteratorSliceIter.next
        change (if h:i<slice.val.length then .ok (some (slice.val[i]'h),⟨slice,i+1⟩)
          else .ok (none,⟨slice,i⟩)) = _
        rw [dif_pos hlt]
      have hb : AspisR1CanonicalStd.all_loop.body inst (⟨slice,i⟩ : core.slice.iter.Iter T) ()=
          .ok (.cont (⟨slice,i+1⟩,())) := by
        simp only [AspisR1CanonicalStd.all_loop.body,hn,bind_tc_ok]
        dsimp only
        rw [hc]
        rfl
      dsimp only
      rw [hb]
      exact ih (i+1) (by omega) (by omega)

#print axioms source_true
end AspisR1.CuSavingsCanonicalDotsAll
