import PreweightedListSemantic

/-! Join the two actual schedule packing calls using the already checked
zero-padded interval concatenation and generic pack4 linearity proofs. -/
set_option autoImplicit false
namespace AspisR1.SchedulePacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueLaneIntervalJoin

theorem pack_append_ofFn {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) {n m : Nat} (start group : Nat)
    (a : Fin n → K) (b : Fin m → K) :
    R0P.pack4 B (fun k : Fin 4 => selectList start (List.ofFn a ++ List.ofFn b) (4*group+k.val)) =
      R0P.pack4 B (fun k : Fin 4 => selectList start (List.ofFn a) (4*group+k.val)) +
      R0P.pack4 B (fun k : Fin 4 => selectList (start+n) (List.ofFn b) (4*group+k.val)) := by
  rw [← ofFn_appendVector]
  simp only [selectList_ofFn]
  exact pack4_selectVector_append B start group a b

def run (packed : Array QM 24#usize) (initial absorption : Array QM 16#usize) :
    Result (Array QM 24#usize) := do
  let packed1 ← AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed 0#usize initial
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed1 16#usize absorption

theorem run_source_list (packed : Array QM 24#usize) (initial absorption : Array QM 16#usize)
    (hp : CanonicalArray packed) (hi : CanonicalArray initial) (ha : CanonicalArray absorption) :
    ∃ out, run packed initial absorption = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) = f (decoded packed j) +
        R0P.pack4 PackB (fun k : Fin 4 => selectList 0
          (List.ofFn (arrayVector initial) ++ List.ofFn (arrayVector absorption)) (4*j.val+k.val)) := by
  obtain ⟨middle, hfirst, hcmiddle, hvfirst⟩ :=
    AspisR1.PreweightedListSemantic.add_preweighted_list packed 0#usize initial
      (by scalar_tac) (by scalar_tac) hp hi
  obtain ⟨out, hsecond, hcout, hvsecond⟩ :=
    AspisR1.PreweightedListSemantic.add_preweighted_list middle 16#usize absorption
      (by scalar_tac) (by scalar_tac) hcmiddle ha
  have h0 : (0#usize).val = 0 := by scalar_tac
  have h16 : (16#usize).val = 16 := by scalar_tac
  simp only [h0] at hvfirst
  simp only [h16] at hvsecond
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [run, hfirst, bind_tc_ok, hsecond]
  · intro j
    rw [hvsecond, hvfirst, add_assoc]
    have hjoin := pack_append_ofFn PackB 0 j.val (arrayVector initial) (arrayVector absorption)
    simp only [Nat.zero_add, h16] at hjoin
    exact congrArg (fun x : Wide => f (decoded packed j) + x) hjoin.symm

#print axioms pack_append_ofFn
#print axioms run_source_list
end
end AspisR1.SchedulePacking
