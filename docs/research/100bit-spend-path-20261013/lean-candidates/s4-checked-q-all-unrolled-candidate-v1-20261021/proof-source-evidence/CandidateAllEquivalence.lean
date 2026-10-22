import AspisR1CheckedQCandidateV1.Funs
import EbyKCheckedQCanonicality

open Aeneas Aeneas.Std Result
namespace AspisR1S4CheckedQCandidateAllEquivalenceV1

abbrev CandidateQ := AspisR1CheckedQCandidateV1.Q

private theorem u32_lt_candidate_p_iff (x : Std.U32) :
    x < 2147483647#u32 ↔ x.val < 2147483647 := by
  simpa only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq]

/-- The Aeneas-emitted four-read/four-comparison candidate has exactly the
    same Option/result behavior as the existing short-circuit allRun model. -/
theorem generated_from_limbs_eq_existing_all_model (x : CandidateQ) :
    AspisR1CheckedQCandidateV1.Q.from_limbs x =
      AspisR1EbyKCheckedQAllParamV1.fromLimbsWithAll
        AspisR1EbyKCheckedQConcreteAll.concreteAll x := by
  rw [AspisR1EbyKCheckedQConcreteAll.fromLimbs_model_eq]
  -- The fixed-length source array contains exactly the four values read by
  -- the emitted index operations; the proof below must retain failure paths.
  cases x with
  | mk xs hx =>
    have hlen : xs.length = 4 := hx
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      cases xs with
      | nil => simp at hlen
      | cons b xs =>
        cases xs with
        | nil => simp at hlen
        | cons c xs =>
          cases xs with
          | nil => simp at hlen
          | cons d xs =>
            cases xs with
            | nil =>
              let v : CandidateQ := ⟨[a,b,c,d], hx⟩
              have h0 : Array.index_usize v 0#usize = .ok a := by
                unfold Array.index_usize
                simp [v]
              have h1 : Array.index_usize v 1#usize = .ok b := by
                unfold Array.index_usize
                simp [v]
              have h2 : Array.index_usize v 2#usize = .ok c := by
                unfold Array.index_usize
                simp [v]
              have h3 : Array.index_usize v 3#usize = .ok d := by
                unfold Array.index_usize
                simp [v]
              change AspisR1CheckedQCandidateV1.Q.from_limbs v = _
              have hA : (a < 2147483647#u32) ↔ a.val < 2147483647 :=
                u32_lt_candidate_p_iff a
              have hB : (b < 2147483647#u32) ↔ b.val < 2147483647 :=
                u32_lt_candidate_p_iff b
              have hC : (c < 2147483647#u32) ↔ c.val < 2147483647 :=
                u32_lt_candidate_p_iff c
              have hD : (d < 2147483647#u32) ↔ d.val < 2147483647 :=
                u32_lt_candidate_p_iff d
              by_cases ha : a.val < 2147483647 <;>
              by_cases hb : b.val < 2147483647 <;>
              by_cases hc : c.val < 2147483647 <;>
              by_cases hd : d.val < 2147483647 <;>
              all_goals simp [AspisR1CheckedQCandidateV1.Q.from_limbs, v,
                h0, h1, h2, h3, ha, hb, hc, hd,
                hA, hB, hC, hD,
                AspisR1CheckedQCandidateV1.P,
                AspisR1EbyKCheckedQConcreteAll.allRun,
                AspisR1EbyKCheckedQAllParamV1.P,
                AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut]

            | cons e xs => simp at hlen

#print axioms generated_from_limbs_eq_existing_all_model
end AspisR1S4CheckedQCandidateAllEquivalenceV1
