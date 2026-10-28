import NDO_JFv_TX2_UpdateMeaning
import RPt_JFs_TX2_Term
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_TermMeaning
open Aeneas Aeneas.Std Result ControlFlow
open JFv_TX2_ArrayMeaning (cell)

def term (n : Nat) : Fin 26 := ⟨n%26,by omega⟩
def product (i : Fin 12) (slot : Fin 4) (j : Fin 8) (n : Nat) : Nat :=
  (cell (JFr_TX2_FirstLane.limbs (term n)) j).val * (JFv_TX2_UpdateMeaning.scalar i slot (term n)).val

theorem source (i : Fin 12) (slot : Fin 4)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound sums n)
    (order : iter.start.val < iter.end.val) (stop : iter.end.val≤26) :
    ∃ next out, next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) iter sums=
        ok (cont (next,out)) ∧ JFs_TX2_ArrayEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell sums j).val+product i slot j iter.start.val := by
  let t : Fin 26 := ⟨iter.start.val,by omega⟩
  have cursor : JFr_TX2_DotTerm.cursor t.val (by have:=t.isLt;omega)=iter.start := by
    apply UScalar.eq_of_val_eq
    unfold JFr_TX2_DotTerm.cursor t
    scalar_tac
  obtain ⟨next,inc,he,body⟩ := JFr_TX2_DotTerm.source i slot t iter.end order
    JFr_TX2_FirstLane.native sums
  obtain ⟨out,run,bound,values⟩ := JFv_TX2_UpdateMeaning.source i slot t sums n hn hs
  unfold JFv_TX2_UpdateMeaning.scalar at run
  rw [run,bind_tc_ok] at body
  rw [cursor] at body
  have same : ({start:=iter.start,«end»:=iter.end} : core.ops.range.Range Usize)=iter := by cases iter;rfl
  rw [same] at body
  have teq : term iter.start.val=t := Fin.ext (Nat.mod_eq_of_lt (by omega))
  refine ⟨next,out,inc,he,body,bound,?_⟩
  intro j
  simpa only [product,teq] using values j
#print axioms source
end AspisR1.JFv_TX2_TermMeaning
end
