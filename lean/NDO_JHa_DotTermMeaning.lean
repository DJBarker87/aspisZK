import NDO_JHa_DotContext
import NDO_JHa_DotUpdateMeaning
import RPt_JFs_TX2_Term
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotTermMeaning
open Aeneas Aeneas.Std Result ControlFlow
open JFv_TX2_ArrayMeaning (cell)

def term (n : Nat) : Fin 26 := ⟨n%26,by omega⟩
def product (d : JHa_DotContext.Data) (j : Fin 8) (n : Nat) : Nat :=
  (cell (JFr_TX2_FirstLane.limbs (term n)) j).val * (d.scalars (term n)).val

theorem source (d : JHa_DotContext.Data)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound sums n)
    (order : iter.start.val < iter.end.val) (stop : iter.end.val≤26) :
    ∃ next out, next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        d.q JFr_TX2_FirstLane.native
        (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) iter sums=
        ok (cont (next,out)) ∧ JFs_TX2_ArrayEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell sums j).val+product d j iter.start.val := by
  let t : Fin 26 := ⟨iter.start.val,by omega⟩
  have cursor : JFr_TX2_DotTerm.cursor t.val (by have:=t.isLt;omega)=iter.start := by
    apply UScalar.eq_of_val_eq
    unfold JFr_TX2_DotTerm.cursor t
    scalar_tac
  obtain ⟨next,inc,he,body⟩ := JGw_DotTerm.source d.q d.slot t (d.scalars t) (d.reads t) iter.end order
    JFr_TX2_FirstLane.native sums
  obtain ⟨out,run,bound,values⟩ := JHa_DotUpdateMeaning.source d t sums n hn hs
  rw [run,bind_tc_ok] at body
  simp only [JGw_DotTerm.cursor] at body
  rw [cursor] at body
  have same : ({start:=iter.start,«end»:=iter.end} : core.ops.range.Range Usize)=iter := by cases iter;rfl
  rw [same] at body
  have teq : term iter.start.val=t := Fin.ext (Nat.mod_eq_of_lt (by omega))
  refine ⟨next,out,inc,he,body,bound,?_⟩
  intro j
  simpa only [product,teq] using values j
#print axioms source
end AspisR1.JHa_DotTermMeaning
end
