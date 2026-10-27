import RPt_JFs_TX2_Update
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Term
open Aeneas Aeneas.Std Result ControlFlow

theorem source (i : Fin 12) (slot : Fin 4)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound sums n)
    (order : iter.start.val < iter.end.val) (stop : iter.end.val≤26) :
    ∃ next out, next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) iter sums=
        ok (cont (next,out)) ∧ JFs_TX2_ArrayEight.Bound out (n+1) := by
  let term : Fin 26 := ⟨iter.start.val,by omega⟩
  have cursor : JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega)=iter.start := by
    apply UScalar.eq_of_val_eq
    unfold JFr_TX2_DotTerm.cursor term
    scalar_tac
  obtain ⟨next,inc,he,body⟩ := JFr_TX2_DotTerm.source i slot term iter.end order
    JFr_TX2_FirstLane.native sums
  obtain ⟨out,run,bound⟩ := JFs_TX2_Update.source i slot term sums n hn hs
  rw [run,bind_tc_ok] at body
  rw [cursor] at body
  have same : ({start:=iter.start,«end»:=iter.end} : core.ops.range.Range Usize)=iter := by cases iter;rfl
  rw [same] at body
  exact ⟨next,out,inc,he,body,bound⟩

#print axioms source
end AspisR1.JFs_TX2_Term
end
