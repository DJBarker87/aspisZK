import JFr_TX2_DotLanes
import JFr_TX2_DotBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_DotLaneTotal
open Aeneas Aeneas.Std Result

theorem extend (x : U32) : (core.convert.num.FromU64U32.from x).val=x.val := by
  simp only [core.convert.num.FromU64U32.from]
  scalar_tac

/-- One real native lane has a successful checked multiply/add/write. The
only input laws are its indexed operands and the explicit four-product bound. -/
theorem source (coefficient : Array U32 8#usize) (scalar word : U32)
    (sums : Array U64 8#usize) (j : Usize) (before : U64) (n : Nat)
    (index : j.val<8)
    (wordRead : Array.index_usize coefficient j=ok word)
    (sumRead : Array.index_usize sums j=ok before)
    (hw : word.val<JFr_TX2_DotBounds.P) (hc : scalar.val<JFr_TX2_DotBounds.P)
    (hn : n<4) (hs : before.val≤n*((JFr_TX2_DotBounds.P-1)*(JFr_TX2_DotBounds.P-1))) :
    ∃ out : U64,
      JFr_TX2_DotLanes.lane coefficient scalar sums j=ok (sums.set j out) ∧
      out.val=before.val+word.val*scalar.val ∧
      out.val≤(n+1)*((JFr_TX2_DotBounds.P-1)*(JFr_TX2_DotBounds.P-1)) := by
  obtain ⟨product,out,hp,ho,vo,bound⟩ := JFr_TX2_DotBounds.add_product
    (core.convert.num.FromU64U32.from word) (core.convert.num.FromU64U32.from scalar)
    before n (by rw [extend];exact hw) (by rw [extend];exact hc) hn hs
  have write : Array.update sums j out=ok (sums.set j out) := by
    obtain ⟨outArray,run,same⟩ := WP.spec_imp_exists
      (Array.update_spec sums j out (by rw [sums.property];exact index))
    exact same ▸ run
  refine ⟨out,?_,?_,bound⟩
  · simp only [JFr_TX2_DotLanes.lane,wordRead,sumRead,lift,bind_tc_ok,hp,ho,write]
  · simpa only [extend] using vo

#print axioms extend
#print axioms source
end AspisR1.JFr_TX2_DotLaneTotal
end
