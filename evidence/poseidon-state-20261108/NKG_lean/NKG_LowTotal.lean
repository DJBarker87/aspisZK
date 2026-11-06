import RPv_FJa_PoseidonLowOnRun
import RPv_JFy_ArrayTotal
import RPv_FIv_PreparedTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_LowTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FJa_PoseidonOrigins (Selectors fullFold internalFold)
theorem callback (s : Selectors) (acc : NQ) (i : Usize) (hs : canonical s.local)
 (hc : Canon acc) (hi : i.val<16) :
 ∃ out,FJa_LocalWeightStep.Call s (acc,i)=ok (out,s) ∧ Canon out := by
 obtain ⟨q,rq,cq⟩ := JFy_ArrayTotal.read s.local i hi hs
 obtain ⟨out,ra,ca,_⟩ := FIv_PreparedTotal.add acc q hc cq
 refine ⟨out,?_,ca⟩
 change (do let v ← Array.index_usize s.local i
            let z ← field.QM31.add acc v
            ok (z,s))=ok (out,s)
 simp only [rq,ra,bind_tc_ok]


theorem fold (N : Usize) (is : List Usize) (s : Selectors) (acc : NQ)
 (hs : canonical s.local) (hc : Canon acc) (bound : ∀ i∈is,i.val<16) :
 ∃ out,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold (N:=N)
   FJa_LocalWeightFold.Callback is acc s=ok out ∧ Canon out := by
 induction is generalizing acc with
 | nil => exact ⟨acc,rfl,hc⟩
 | cons i is ih =>
   obtain ⟨next,rn,cn⟩ := callback s acc i hs hc (bound i (by simp))
   obtain ⟨out,ro,co⟩ := ih next cn (by intro j hj;exact bound j (by simp [hj]))
   refine ⟨out,?_,co⟩
   simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold,rn,bind_tc_ok]
   exact ro

theorem full (s : Selectors) (hs : canonical s.local) : ∃ out,fullFold s=ok out ∧ Canon out := by
 obtain ⟨out,run,co⟩ := fold 3#usize [1#usize,9#usize,10#usize] s field.QM31.ZERO hs
   FIv_NativeValue.zero.1 (by intro i hi;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl|rfl|rfl <;> decide)
 refine ⟨out,?_,co⟩
 simpa only [fullFold,FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
   Array.make,bind_tc_ok] using run

theorem internal (s : Selectors) (hs : canonical s.local) : ∃ out,internalFold s=ok out ∧ Canon out := by
 rw [FJa_InternalLowShape.value]
 exact fold 7#usize [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize] s field.QM31.ZERO hs
   FIv_NativeValue.zero.1 (by intro i hi;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
#print callback
#print axioms callback
#print fold
#print axioms fold
#print full
#print axioms full
#print internal
#print axioms internal
end AspisR1.NKG_LowTotal
end
