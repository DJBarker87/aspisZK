import RPu_FIv_PreparedMul
import RPu_FIv_CompositionTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_Horner4
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP prepared)
abbrev loop := FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
def model (theta : K) (xs : List NQ) (seed : K) : K :=
  xs.foldl (fun acc lane=>theta*acc+decode lane) seed

theorem value (xs : List NQ) (p : NP) (theta seed out : NQ)
    (ht : Canon theta) (hs : Canon seed)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta))
    (hc : ∀ x∈xs,Canon x)
    (run : loop ⟨xs.reverse⟩ p seed=ok out) :
    Canon out ∧ decode out=model (decode theta) xs (decode seed) := by
  induction xs generalizing seed with
  | nil =>
    rw [loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1] at run
    simp only [List.reverse_nil,
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      List.reverse_nil,bind_tc_ok] at run
    have same := Result.ok.inj run
    subst out
    exact ⟨hs,rfl⟩
  | cons x xs ih =>
    rw [loop,FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1] at run
    simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      List.reverse_reverse,bind_tc_ok] at run
    obtain ⟨product,hm,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨next,ha,run⟩ := FIv_Map.bind_success _ _ _ run
    have productValue := FIv_PreparedMul.value p theta seed product ht hs hp hm
    have nextValue := FIv_NativeValue.add product x next productValue.1 (hc x (by simp)) ha
    have rest := ih next nextValue.1 (fun y hy=>hc y (by simp only [List.mem_cons];exact Or.inr hy)) run
    refine ⟨rest.1,?_⟩
    rw [rest.2,nextValue.2,productValue.2]
    rfl
#print axioms value
end AspisR1.FIv_Horner4
end
