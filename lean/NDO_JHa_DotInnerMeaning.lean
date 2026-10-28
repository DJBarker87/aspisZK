import NDO_JHa_DotContext
import NDO_JHa_DotTermMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotInnerMeaning
open Aeneas Aeneas.Std Result ControlFlow
open JFv_TX2_ArrayMeaning (cell)

def sum (d : JHa_DotContext.Data) (j : Fin 8) (base : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum d j base n+JHa_DotTermMeaning.product d j (base+n)

def Inv (d : JHa_DotContext.Data) (base stop : Nat)
    (state : core.ops.range.Range Usize × Array U64 8#usize) : Prop :=
  state.1.end.val=stop ∧ base ≤ state.1.start.val ∧ state.1.start.val ≤ stop ∧
  JFs_TX2_ArrayEight.Bound state.2 (state.1.start.val-base) ∧
  ∀ j : Fin 8, (cell state.2 j).val=sum d j base (state.1.start.val-base)

theorem source (d : JHa_DotContext.Data) (iter : core.ops.range.Range Usize)
    (order : iter.start.val ≤ iter.end.val) (stop : iter.end.val ≤ 26)
    (width : iter.end.val ≤ iter.start.val+4) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter
      d.q JFr_TX2_FirstLane.native
      (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)=ok out ∧
      JFs_TX2_ArrayEight.Bound out (iter.end.val-iter.start.val) ∧
      ∀ j : Fin 8, (cell out j).val=sum d j iter.start.val (iter.end.val-iter.start.val) := by
  have spec : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter
      d.q JFr_TX2_FirstLane.native
      (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) (Array.repeat 8#usize 0#u64)
      ⦃ out => JFs_TX2_ArrayEight.Bound out (iter.end.val-iter.start.val) ∧
        ∀ j : Fin 8, (cell out j).val=sum d j iter.start.val (iter.end.val-iter.start.val) ⦄ := by
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    refine loop.spec_decr_nat
      (fun state : core.ops.range.Range Usize × Array U64 8#usize => iter.end.val-state.1.start.val)
      (Inv d iter.start.val iter.end.val) _
      (fun (r,s) => FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        d.q JFr_TX2_FirstLane.native
        (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) r s)
      (iter,Array.repeat 8#usize 0#u64) ?_ ?_
    · rintro ⟨r,s⟩ ⟨he,hb,ho,hs,values⟩
      dsimp only at he hb ho hs values ⊢
      by_cases running : r.start.val < r.end.val
      · obtain ⟨next,out,inc,ending,run,bound,stepval⟩ := JHa_DotTermMeaning.source d r s
          (r.start.val-iter.start.val) (by omega) hs running (by omega)
        rw [run,WP.spec_ok]
        refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
        · simpa only [ending] using he
        · dsimp only;omega
        · dsimp only;omega
        · change JFs_TX2_ArrayEight.Bound out (next.start.val-iter.start.val)
          convert bound using 1  <;> omega
        · intro j
          change (cell out j).val=sum d j iter.start.val (next.start.val-iter.start.val)
          rw [stepval j,values j,show next.start.val-iter.start.val=(r.start.val-iter.start.val)+1 by omega,sum]
          congr 2
          omega
        · dsimp only;omega
      · obtain ⟨⟨o,next⟩,run,none,_⟩ := WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_UScalar_none_spec
            (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
            (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b;rfl) r (by omega))
        subst o
        unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        rw [run]
        simp only [bind_tc_ok,Aeneas.Std.uncurry,WP.spec_ok]
        have done : r.start.val=iter.end.val := by omega
        simpa only [done] using And.intro hs values
    · dsimp only [Inv]
      refine ⟨rfl,by omega,order,?_,?_⟩
      · intro x hx
        have same : x=0#u64 := (List.mem_replicate.mp hx).2
        subst x
        simp
      · intro j
        rw [Nat.sub_self]
        fin_cases j <;> rfl
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JHa_DotInnerMeaning
end
