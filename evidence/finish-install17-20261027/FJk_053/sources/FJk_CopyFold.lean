import FJk_CopyStep
import FJk_CopyRegistry
import FIr_ArrayRead
import FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyFold
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
attribute [local irreducible] constants.COPY_LINKS R0P.copyLinks FJk_CopyStep.step
/-- Symbolic induction over the actual link-index suffix, never concrete loop reduction. -/
theorem value (n : Nat) (i : Usize) (s : Selectors) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (patterns : Array field.QM31 14#usize)
    (pv pw cv cw a b c d : Array field.QM31 2#usize) (span : i.val+n=136)
    (hh : canonical s.high) (hl : canonical s.low) (hp : canonical patterns)
    (hpv : canonical pv) (hpw : canonical pw) (hcv : canonical cv) (hcw : canonical cw)
    (run : evaluate_with_selectors_loop s index v patterns pv pw cv cw i=ok (a,b,c,d)) :
    canonical a ∧ canonical b ∧ canonical c ∧ canonical d ∧
      FJk_CopyStep.row a b c d=
      (constants.COPY_LINKS.val.drop i.val).foldl
        (fun r l=>FJk_CopyStep.step (FIw_CopyEndpoint.modelSelectors s) (decoded patterns)
          index.val (FJk_CopyDescriptor.variant v) r (FJk_CopyDescriptor.link l))
        (FJk_CopyStep.row pv pw cv cw) := by
  induction n generalizing i pv pw cv cw with
  | zero =>
    have stop : ¬i<136#usize := by scalar_tac
    rw [evaluate_with_selectors_loop,POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1,if_neg stop] at run
    have same : pv=a ∧ pw=b ∧ cv=c ∧ cw=d := by
      simpa only [Prod.mk.injEq] using Result.ok.inj run
    obtain ⟨rfl,rfl,rfl,rfl⟩ := same
    refine ⟨hpv,hpw,hcv,hcw,?_⟩
    rw [List.drop_eq_nil_of_le (by rw [constants.COPY_LINKS.property];change 136≤i.val;omega)]
    rfl
  | succ n ih =>
    have active : i<136#usize := by scalar_tac
    rw [evaluate_with_selectors_loop,POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1,if_pos active] at run
    obtain ⟨l,rl,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨w,rwgt,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨pv',pw'⟩,rp,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨cv',cw'⟩,rc,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i',ri,tail⟩ := FIv_Map.bind_success _ _ _ run
    have hg := JGa_LinkBounds.all l (FIr_ArrayRead.member constants.COPY_LINKS i l rl)
    have one := FJk_CopyStep.value pv pw cv cw pv' pw' cv' cw' l index v patterns s w
      hpv hpw hcv hcw hp hh hl hg rwgt rp rc
    have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' ri
    have rest := ih i' pv' pw' cv' cw' (by omega) one.1 one.2.1 one.2.2.1 one.2.2.2.1 tail
    refine ⟨rest.1,rest.2.1,rest.2.2.1,rest.2.2.2.1,?_⟩
    have bound : i.val<constants.COPY_LINKS.val.length := by rw [constants.COPY_LINKS.property];change i.val<136;omega
    have at : constants.COPY_LINKS.val[i.val]'bound=l := by
      have slot := FIr_ArrayRead.slot constants.COPY_LINKS i l rl
      simpa only [List.getElem?_eq_getElem bound,Option.some.injEq] using slot
    rw [List.drop_eq_getElem_cons bound,at,List.foldl_cons,rest.2.2.2.2,inc,one.2.2.2.2]
#print axioms value
end AspisR1.FJk_CopyFold
end
