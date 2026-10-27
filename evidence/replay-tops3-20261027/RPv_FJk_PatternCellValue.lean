import RPv_FJk_CopyPatternDescriptor
import RPv_FJk_CarrierRead
import RPv_FJk_PatternDescriptorReads
import RPv_JGa_PatternCell
import RPv_FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternCellValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
attribute [local irreducible] FJk_CopyPatternDescriptor.model
def step (a powers : Array field.QM31 16#usize) (p : R0P.CopyPattern)
    (i : Fin 16) (value : K) : K :=
  if p.kinds i=1 then value+FIv_NativeArray.value powers i.val*
    (FIv_NativeArray.value a (p.columns i).val+(p.offsets i : K)) else value
/-- VALUE of the actual pattern cell, retaining its original field arithmetic. -/
theorem value (a powers : Array field.QM31 16#usize) (p : CompiledPoolV1PairForestPattern)
    (i : Usize) (before out : field.QM31) (hi : i.val<16)
    (ha : canonical a) (hp : canonical powers) (hb : Canon before)
    (hg : JGa_PatternBounds.Good p)
    (run : JGa_PatternCell.run a powers i p before=ok out) :
    Canon out ∧ decode out=step a powers (FJk_CopyPatternDescriptor.model p) ⟨i.val,hi⟩ (decode before) := by
  unfold JGa_PatternCell.run at run
  obtain ⟨kind,rkind,run⟩ := FIv_Map.bind_success _ _ _ run
  have vk := FJk_PatternDescriptorReads.kinds p i hi kind rkind
  split at run
  · rename_i hk
    obtain ⟨col,rcol,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨idx,ridx,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨offset,roff,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨lifted,rlift,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨source,rsource,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨power,rpower,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨product,rproduct,run⟩ := FIv_Map.bind_success _ _ _ run
    have cb := hg.1 col (FIr_ArrayRead.member p.columns i col rcol)
    have vc := FJk_PatternDescriptorReads.columns p i hi col cb rcol
    have vo := FJk_PatternDescriptorReads.offsets p i hi offset roff
    have ob := hg.2 offset (FIr_ArrayRead.member p.offsets i offset roff)
    have ix : idx.val=col.val := by cases Result.ok.inj ridx;exact core.convert.num.FromUsizeU8.from_val_eq col
    change pool_v1.pair_forest_semantic_terminal.lift_m31 offset=ok lifted at rlift
    rw [FIw_ScalarArithmetic.lift_run] at rlift
    have lifted_eq : lifted=FIw_ScalarArithmetic.lifted offset := (Result.ok.inj rlift).symm
    have lv : Canon lifted ∧ decode lifted=(offset.val : K) := by
      rw [lifted_eq]
      exact FIw_ScalarArithmetic.lift_value offset ob
    have qv := FIv_NativeArray.canonical a idx q ha rq
    have pw := FIv_NativeArray.canonical powers i power hp rpower
    have sv := FIv_NativeValue.add q _ source qv lv.1 rsource
    have mv := FIv_NativeValue.mul power source product pw sv.1 rproduct
    have result := FIv_NativeValue.add before product out hb mv.1 run
    refine ⟨result.1,?_⟩
    rw [result.2,mv.2,sv.2,lv.2,←FIv_NativeArray.read a idx q rq,
      ←FIv_NativeArray.read powers i power rpower,ix]
    unfold step
    rw [vk,vc,vo,hk]
    simp only [UScalar.ofNatCore_val_eq,ite_true]
  · rename_i hk
    have same := Result.ok.inj run
    subst out
    refine ⟨hb,?_⟩
    unfold step
    rw [vk]
    have kn : kind.val≠1 := by intro h;exact hk (UScalar.eq_of_val_eq h)
    rw [if_neg kn]
#print axioms value
end AspisR1.FJk_PatternCellValue
end
