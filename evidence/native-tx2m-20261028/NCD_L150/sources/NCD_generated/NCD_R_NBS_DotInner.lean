-- Retargeted inherited proof body; only module imports changed.
import NCD_R_NBS_DotTerm
set_option autoImplicit false
noncomputable section
namespace NBS_DotInner
open Aeneas Aeneas.Std Result ControlFlow AspisR1

def Inv (base stop : Nat) (state : core.ops.range.Range Usize × Array U64 8#usize) : Prop :=
  state.1.end.val=stop ∧ base≤state.1.start.val ∧ state.1.start.val≤stop ∧
    JFs_TX2_ArrayEight.Bound state.2 (state.1.start.val-base)

theorem source (q : Array U8 608#usize) (slot : Usize) (decoded : NBS_DotTerm.Scalars q slot)
    (g : Array AspisR1.FIo_Install.NE 29#usize) (hg : AspisR1.FIo_ArrayCanon.Holds g) (iter : core.ops.range.Range Usize)
    (sums : Array U64 8#usize) (base : Nat)
    (hbase : base≤ iter.start.val) (horder : iter.start.val≤ iter.end.val)
    (hstop : iter.end.val≤26) (width : iter.end.val≤base+4)
    (hs : JFs_TX2_ArrayEight.Bound sums (iter.start.val-base)) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter
      q g slot sums=ok out ∧
      JFs_TX2_ArrayEight.Bound out (iter.end.val-base) := by
  have spec : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter
      q g slot sums
      ⦃ out => JFs_TX2_ArrayEight.Bound out (iter.end.val-base) ⦄ := by
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    refine loop.spec_decr_nat
      (fun state : core.ops.range.Range Usize × Array U64 8#usize => iter.end.val-state.1.start.val)
      (Inv base iter.end.val) (fun out => JFs_TX2_ArrayEight.Bound out (iter.end.val-base))
      (fun (r,s) => FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        q g slot r s)
      (iter,sums) ?_ ⟨rfl,hbase,horder,hs⟩
    rintro ⟨r,s⟩ ⟨he,hb,ho,hs⟩
    dsimp only at he hb ho hs ⊢
    by_cases running : r.start.val < r.end.val
    · obtain ⟨next,out,inc,stop,run,bound⟩ := NBS_DotTerm.source q slot decoded g hg r s
        (r.start.val-base) (by omega) hs running (by omega)
      rw [run,WP.spec_ok]
      change Inv base iter.end.val (next,out) ∧ iter.end.val-next.start.val < iter.end.val-r.start.val
      dsimp only [Inv]
      refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
      · simpa only [stop] using he
      · omega
      · have he' : next.end.val=r.end.val := congrArg UScalar.val stop
        omega
      · change JFs_TX2_ArrayEight.Bound out (next.start.val-base)
        convert bound using 1 <;> omega
      · omega
    · have same : r.start.val=r.end.val := by omega
      unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
      step*
      all_goals first | scalar_tac | (simpa only [same,he] using hs)
  exact WP.spec_imp_exists spec

#print axioms source
end NBS_DotInner
end
