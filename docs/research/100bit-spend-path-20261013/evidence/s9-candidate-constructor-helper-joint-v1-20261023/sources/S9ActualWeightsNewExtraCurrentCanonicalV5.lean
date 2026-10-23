import AspisR1S9ActualWeightsNewBoxNewV1.Funs
import S9ActualWeightsNewExtraExactV6
import AspisR1S9PairCallerStepV1.FunsExternal
import KpowersCurrentQMSemanticsV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1S9ActualWeightsNewBoxNewV1

namespace AspisR1S9ActualWeightsNewExtraCurrentCanonicalV5


/-- Structural carrier map from the actual extracted constructor's QM type to
 the selected Pair caller's QM type. The four limbs are unchanged. -/
def candidateToPairM (x : AspisR1S9ActualWeightsNewBoxNewV1.field.M31) : AspisR1S9PairCallerStepV1.field.M31 := x
def candidateToPairCM (x : AspisR1S9ActualWeightsNewBoxNewV1.field.CM31) : AspisR1S9PairCallerStepV1.field.CM31 :=
  ⟨candidateToPairM x.a, candidateToPairM x.b⟩
def candidateToPairQM (x : AspisR1S9ActualWeightsNewBoxNewV1.field.QM31) : AspisR1S9PairCallerStepV1.field.QM31 :=
  ⟨candidateToPairCM x.c0, candidateToPairCM x.c1⟩

def candidateToCurrentQM (x : AspisR1S9ActualWeightsNewBoxNewV1.field.QM31) :
    AspisR1CurrentWide.field.QM31 :=
  AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
    (AspisR1S9PairCallerStepV1.toP6Q (candidateToPairQM x))

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- The same successful Box::new constructor run returns exactly the two
actual `alpha[8]` and `alpha[9]` reads. If those reads satisfy the existing
selected-carrier canonicality contract, every successful read from the full
returned extra array is canonical. The `halpha` premise is deliberately the
source-model/caller contract; it does not claim the Rust caller-to-model join. -/
theorem weights_new_extra_current_fullread_canonical_v5
    (variant : Variant)
    (alpha : Array AspisR1S9ActualWeightsNewBoxNewV1.field.QM31 (10#usize))
    (z : Array AspisR1S9ActualWeightsNewBoxNewV1.circle.SecureCirclePoint (2#usize))
    (w : Weights)
    (hnew : weights_new variant alpha z = .ok (core.result.Result.Ok w))
    (halpha : ∀ (i : Std.Usize) (q : AspisR1S9PairCallerStepV1.field.QM31),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray candidateToPairQM alpha) i = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM (AspisR1S9PairCallerStepV1.toP6Q q))) :
    ∃ q8 q9,
      Array.index_usize alpha 8#usize = .ok q8 ∧
      Array.index_usize alpha 9#usize = .ok q9 ∧
      w.extra = Array.make 2#usize [q8, q9] ∧
      ∀ (j : Std.Usize) (v : AspisR1CurrentWide.field.QM31),
        Array.index_usize
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray candidateToCurrentQM w.extra) j = .ok v →
        AspisR1CurrentWide.Proof.CanonicalQM v := by
  obtain ⟨q8, q9, h8, h9, hextra⟩ :=
    AspisR1S9ActualWeightsNewExtraExactV6.weights_new_extra_exact_v6
      variant alpha z w hnew
  have hm8 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    candidateToPairQM alpha 8#usize
  have hm9 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    candidateToPairQM alpha 9#usize
  rw [h8] at hm8
  rw [h9] at hm9
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hm8 hm9
  have hcan8 : AspisR1CurrentWide.Proof.CanonicalQM (candidateToCurrentQM q8) := by
    simpa only [candidateToCurrentQM] using
      halpha 8#usize (candidateToPairQM q8) hm8.symm
  have hcan9 : AspisR1CurrentWide.Proof.CanonicalQM (candidateToCurrentQM q9) := by
    simpa only [candidateToCurrentQM] using
      halpha 9#usize (candidateToPairQM q9) hm9.symm
  refine ⟨q8, q9, h8, h9, hextra, ?_⟩
  intro j v hread
  have hmapExtra :
      AspisR1S9CandidateFoldMapPrimitivesV1.mapArray candidateToCurrentQM w.extra =
        Array.make 2#usize [candidateToCurrentQM q8, candidateToCurrentQM q9] := by
    rw [hextra]
    rfl
  rw [hmapExtra] at hread
  have hjbound := index_success_bound
    (Array.make 2#usize [candidateToCurrentQM q8, candidateToCurrentQM q9]) j v hread
  have htwo : (2#usize).val = 2 := by decide
  have hjcases : j.val = 0 ∨ j.val = 1 := by omega
  rcases hjcases with hj0 | hj1
  · have hj : j = 0#usize := UScalar.eq_of_val_eq (by simpa using hj0)
    subst j
    have hvalue : v = candidateToCurrentQM q8 := by
      have heq : Array.index_usize
          (Array.make 2#usize [candidateToCurrentQM q8, candidateToCurrentQM q9])
          0#usize = .ok (candidateToCurrentQM q8) := rfl
      exact Result.ok.inj (hread.symm.trans heq)
    simpa [hvalue] using hcan8
  · have hj : j = 1#usize := UScalar.eq_of_val_eq (by simpa using hj1)
    subst j
    have hvalue : v = candidateToCurrentQM q9 := by
      have heq : Array.index_usize
          (Array.make 2#usize [candidateToCurrentQM q8, candidateToCurrentQM q9])
          1#usize = .ok (candidateToCurrentQM q9) := rfl
      exact Result.ok.inj (hread.symm.trans heq)
    simpa [hvalue] using hcan9

#print axioms weights_new_extra_current_fullread_canonical_v5

end AspisR1S9ActualWeightsNewExtraCurrentCanonicalV5
