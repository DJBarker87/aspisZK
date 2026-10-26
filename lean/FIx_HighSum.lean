import FIx_HighSumOuter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_HighSum
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIx_HighSumInner (Selectors Range)

theorem source (s : Selectors) (rs : Slice Range)
    (bounds : ∀ r∈rs.val,r.start.val≤r.end.val ∧ r.end.val≤64)
    (hh : ∀ x∈s.high.val,Canon x) :
    ∃ out,pool_v1.pair_forest_semantic_terminal.sum_high s rs=ok out ∧
      Canon out ∧ decode out=FIx_HighSumOuter.ranges rs.val s 0 := by
  obtain ⟨out,hr,hc,hv⟩ := FIx_HighSumOuter.value rs.val ⟨rs,0⟩ s field.QM31.ZERO
    (by simp) bounds hh FIv_NativeValue.zero.1
  refine ⟨out,?_,hc,?_⟩
  · unfold pool_v1.pair_forest_semantic_terminal.sum_high
    simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_tc_ok]
    exact hr
  · rw [FIv_NativeValue.zero.2] at hv
    exact hv

theorem value (s : Selectors) (rs : Slice Range) (out : NQ)
    (bounds : ∀ r∈rs.val,r.start.val≤r.end.val ∧ r.end.val≤64)
    (hh : ∀ x∈s.high.val,Canon x)
    (run : pool_v1.pair_forest_semantic_terminal.sum_high s rs=ok out) :
    Canon out ∧ decode out=FIx_HighSumOuter.ranges rs.val s 0 := by
  obtain ⟨out1,hr,hc,hv⟩ := source s rs bounds hh
  cases Result.ok.inj (run.symm.trans hr)
  exact ⟨hc,hv⟩
#print axioms source
#print axioms value
end AspisR1.FIx_HighSum
end
