import S4CurrentHeadTermForwardRootV1
import BatchedWeightsFlushPrimitiveV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsLimbFoldForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cell)
abbrev LimbBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body
abbrev LimbLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
abbrev limbCap : Nat := 2^34-1

private theorem bind_success {α β : Type} (m : Result α) (f : α→Result β) (v : β)
    (h : (do let x←m; f x) = .ok v) : ∃ x, m=.ok x ∧ f x=.ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem limb_body_forward
    (ops : Ops) (sums limbs : Array Std.U64 8#usize) (iter iter' : Range)
    (limb : Usize) (b : Nat) (hb : b≤64)
    (hi : limb.val<8)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some limb,iter'))
    (hinput : ∀ j : Fin 8, cell limbs j≤b*limbCap) :
    ∃ out : Array Std.U64 8#usize,
      LimbBody ops sums iter limbs = .ok (.cont (iter',out)) ∧
      (∀ j : Fin 8, cell out j≤(b+1)*limbCap) := by
  obtain ⟨x,hr,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec sums limb (by simpa [Array.length,sums.property] using hi))
  obtain ⟨old,hor,hov⟩ := WP.spec_imp_exists
    (Array.index_usize_spec limbs limb (by simpa [Array.length,limbs.property] using hi))
  have hold : old.val≤b*limbCap := by
    rw [hov]
    exact hinput ⟨limb.val,hi⟩
  obtain ⟨part,hflush,hpart⟩ := BatchedWeightsFlushPrimitiveV2.generatedFlush_success x
  have hp : part.val≤limbCap := by
    rw [hpart]
    have hf := AspisR1BatchedFoldSourceStep.fold_lt_two34 (show x.val<2^64 from x.bv.isLt)
    change AspisR1BatchedFoldSourceStep.fold x.val≤2^34-1
    omega
  have hsum : old.val+part.val<2^64 := by
    have hcap : 65*limbCap<2^64 := by norm_num [limbCap]
    have hbound := Nat.mul_le_mul_right limbCap hb
    omega
  obtain ⟨value,hadd,hval⟩ := AspisR1.ExtractedCurrentReducerOps.add_success old part hsum
  have haddTyped : (old+part : Result Std.U64)=.ok value := by
    change UScalar.add _ _=.ok value
    exact hadd
  obtain ⟨out,hu,hset⟩ := WP.spec_imp_exists
    (Array.update_spec limbs limb value (by simpa [Array.length,limbs.property] using hi))
  have hvalue : value.val≤(b+1)*limbCap := by
    rw [hval,Nat.add_mul,Nat.one_mul]
    omega
  have hglobal : ∀ j : Fin 8, cell limbs j≤(b+1)*limbCap := by
    intro j
    exact le_trans (hinput j) (Nat.mul_le_mul_right limbCap (Nat.le_succ b))
  have hout : ∀ j : Fin 8, cell out j≤(b+1)*limbCap := by
    rw [hset]
    exact AspisR1FastDotsActualLimbPrefixStepV2.set_preserves_pointwise_bound
      limbs limb value ((b+1)*limbCap) hglobal hvalue
  have hbody : LimbBody ops sums iter limbs=.ok (.cont (iter',out)) := by
    simp only [LimbBody,
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn,bind_tc_ok,hr]
    obtain ⟨low,hlow,hrest⟩ := bind_success _ _ _ hflush
    obtain ⟨high,hhigh,hfold⟩ := bind_success _ _ _ hrest
    change ((do
      let y ← Array.index_usize sums limb
      let lo ← lift (y &&& 2147483647#u64)
      let high ← y >>> 31#i32
      let folded ← lo+high
      let oldVal ← Array.index_usize limbs limb
      let newVal ← oldVal+folded
      let updated ← Array.update limbs limb newVal
      .ok (.cont (iter',updated))) : Result (ControlFlow
        (Range × Array Std.U64 8#usize) (Array Std.U64 8#usize))) = .ok (.cont (iter',out))
    simp only [hr,hlow,hhigh,bind_tc_ok,hfold,hor,haddTyped,hu]
  exact ⟨out,hbody,hout⟩

#print axioms limb_body_forward
end AspisR1FastDotsLimbFoldForwardRootV1
