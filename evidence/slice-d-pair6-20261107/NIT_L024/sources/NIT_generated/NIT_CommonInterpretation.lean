import NIT_LowInterpretation
import NIT_IndexLemmas
set_option autoImplicit false
namespace AspisR1.NIT_CommonInterpretation
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

theorem kpick_index {n : Usize} (xs : Array K n) (i : Usize) (small : i.val<n.val) :
 Array.index_usize xs i=ok (kpick xs i.val) := by
 rw [NHI_ScalarDomain.index xs i small]
 have bound : i.val<xs.val.length := by rw [xs.property];exact small
 simp only [kpick,List.getElem?_eq_getElem bound,Option.getD_some,NHI_ScalarDomain.pick]

theorem kpick_canonical {n : Usize} (xs : Array K n) (hc : NHI_CellCanon.array xs)
 (i : Nat) (small : i<n.val) : canonQ (kpick xs i) := by
 have bound : i<xs.val.length := by rw [xs.property];exact small
 simp only [kpick,List.getElem?_eq_getElem bound,Option.getD_some]
 exact hc _ (List.getElem_mem bound)

/-- The exact QM31 call is interpreted on the SAME two selected rows. -/
theorem window (row2 row3 : Array K 4#usize) (j : Usize)
 (h2 : NHI_CellCanon.array row2) (h3 : NHI_CellCanon.array row3)
 (before after : CommonCells) (l : Common)
 (cut : cutCommon row2 row3 j.val before l after)
 (law : QMul l.lhs l.rhs l.reply) :
 (do let product ← FIo_Native.aspis_core.field.QM31.mul
       (kpick row2 (j.val%4)) (kpick row3 (j.val/4))
     Array.update before j product)=ok after ∧ canonQ l.reply := by
 have frame := common_frame row2 row3 j.val before after l cut
 rcases cut with ⟨small,lh,rh,_,_⟩
 have c2 := kpick_canonical row2 h2 (j.val%4) (by change j.val%4<4;omega)
 have c3 := kpick_canonical row3 h3 (j.val/4) (by change j.val/4<4;omega)
 have product := qm l.lhs l.rhs l.reply (lh.symm ▸ c2) (rh.symm ▸ c3) law
 rw [lh,rh] at product
 refine ⟨?_,product.2⟩
 simp only [product.1,bind_tc_ok]
 rw [frame]
 exact NIT_LowInterpretation.update_model before j l.reply small

/-- Associate that window to the actual emitted Common body, including mask,
shift, row selection, destination and the unchanged owner. -/
theorem step (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (s : NHX_CommonDomain.State) (after : CommonCells) (l : Common)
 (cut : cutCommon
  (NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors 0 (by decide)) 2 (by decide))
  (NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors 0 (by decide)) 3 (by decide))
  s.1.start.val s.2 l after)
 (law : QMul l.lhs l.rhs l.reply) (last : s.1.end.val=16) :
 ∃ rest,NHX_CommonDomain.body w s=ok (.cont (rest,after)) ∧
 rest.end.val=16 ∧ rest.start.val=s.1.start.val+1 := by
 let rows := NHI_ScalarDomain.pick w.factors 0 (by decide)
 let row2 := NHI_ScalarDomain.pick rows 2 (by decide)
 let row3 := NHI_ScalarDomain.pick rows 3 (by decide)
 have small := cut.1
 obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
 have cell := window row2 row3 s.1.start (hf 0 (by decide) 2 (by decide))
  (hf 0 (by decide) 3 (by decide)) s.2 after l cut law
 have lo := NIT_IndexLemmas.mask s.1.start
 have hi := NIT_IndexLemmas.shift s.1.start
 refine ⟨rest,?_,by rw [he];exact last,inc⟩
 simp only [NHX_CommonDomain.body,FIo_Native.weights.Weights.pair_loop1.body,next,bind_tc_ok]
 dsimp! only
 simp only [NHI_ScalarDomain.index w.factors 0#usize (by decide),
  NHI_ScalarDomain.index rows 2#usize (by decide),
  NHI_ScalarDomain.index rows 3#usize (by decide),bind_tc_ok]
 simp only [kpick_index row2 (s.1.start &&& 3#usize) (by rw [lo];change s.1.start.val%4<4;omega),
  kpick_index row3 (Usize.wrapping_shr s.1.start 2#u32) (by rw [hi];change s.1.start.val/4<4;omega),
  lo,hi,bind_tc_ok]
 exact cell.1

#print axioms kpick_index
#print axioms kpick_canonical
#print axioms window
#print axioms step
end AspisR1.NIT_CommonInterpretation
