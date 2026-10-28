import RPv_FIv_PreparedTotal
import RPv_FIv_Horner4
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_Horner4Total
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP prepared)
open FIv_Horner4 (loop model)
theorem value (xs : List NQ) (p : NP) (theta seed : NQ)
    (ht : Canon theta) (hs : Canon seed)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta))
    (hc : ∀ x∈xs,Canon x) :
    ∃ out, loop ⟨xs.reverse⟩ p seed=ok out ∧
      Canon out ∧ decode out=model (decode theta) xs (decode seed) := by
  induction xs generalizing seed with
  | nil =>
    refine ⟨seed,?_,hs,rfl⟩
    rw [FIv_Horner4.loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1]
    simp only [List.reverse_nil,
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      List.reverse_nil,bind_tc_ok]
    rfl
  | cons x xs ih =>
    obtain ⟨product,hm,hpc,hpv⟩ := FIv_PreparedTotal.mul p theta seed ht hs hp
    obtain ⟨next,ha,hnc,hnv⟩ := FIv_PreparedTotal.add product x hpc (hc x (by simp))
    obtain ⟨out,run,hoc,hov⟩ := ih next hnc (fun y hy=>hc y (by simp only [List.mem_cons];exact Or.inr hy))
    refine ⟨out,?_,hoc,?_⟩
    · rw [FIv_Horner4.loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1]
      simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        List.reverse_reverse,bind_tc_ok]
      change (do
        let prod ← FIq_Native.field.PreparedQm31Multiplier.mul p seed
        let nxt ← FIq_Native.field.QM31.add prod x
        FIv_Horner4.loop ⟨xs.reverse⟩ p nxt)=ok out
      rw [hm,bind_tc_ok,ha,bind_tc_ok]
      exact run
    · rw [hov,hnv,hpv]
      rfl
#print axioms value
end AspisR1.FIv_Horner4Total
end
