import R0P.MaskBadSets

/-! Sampler density of every masked semantic row, with the candidate factor
100 on eta and alpha. These bounds are prior to the duplex D2 transfer. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 R0C.SemStatement R0P R0P.SemSource R0P.SemD3Glue R0P.Sumcheck Polynomial
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.SourceDuplexStep
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal prefix classifier has the authorized per-row sampler bound. -/
theorem semantic_round_densityZ {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE}
    (maskClaims : (Fin 29 → SemE) → (Fin 10 → SemE) → SemE) (B : PackBasis F)
    (P : Prefix SemE SemE (TypedContext SemE Sfield) (SemMsgZ SemE)) (sm : SemMsgZ SemE)
    (hi : P.rounds.length < 25) :
    mean (fun s : State => indicator (semanticBadZ maskClaims B P sm (semChal s))) ≤
      combinedD2BudgetZ P.rounds.length := by
  have hq : 0 ≤ (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 :=
    div_nonneg (add_nonneg zero_le_one deltaQ_nonneg) (pow_nonneg (Nat.cast_nonneg _) _)
  have hz (h : ∀ c, ¬ semanticBadZ maskClaims B P sm c) :
      mean (fun s : State => indicator (semanticBadZ maskClaims B P sm (semChal s))) = 0 := by
    rw [mean_congr (fun s => indicator_iff (iff_false_intro (h (semChal s))))]
    simp only [indicator_false, mean_const]
  by_cases h14 : P.rounds.length < 14
  · rw [combinedD2BudgetZ, if_pos h14]
    have hb := semantic_round_density B ⟨P.statement, baseRoundsZ P.rounds⟩ (unmaskSem sm)
      (by simp only [baseRoundsZ, List.length_map]; omega)
    simp only [baseRoundsZ, List.length_map] at hb
    simp only [combinedD2Budget, dif_pos (show P.rounds.length < 24 by omega)]
    apply le_trans _ hb
    apply mean_mono
    intro s
    apply indicator_mono
    intro h
    simpa only [semanticBadZ, dif_pos h14, baseRoundsZ] using h.2
  · rw [combinedD2BudgetZ, if_neg h14]
    by_cases heq : P.rounds.length = 14
    · rw [if_pos heq]
      cases sm with
      | base m =>
          rw [hz (by intro c h; simpa only [semanticBadZ, dif_neg h14, if_pos heq] using h.2)]
          exact mul_nonneg (by norm_num) hq
      | maskSum claim =>
          cases hcs : semChalsZ P.rounds with
          | none =>
              rw [hz (by intro c h; simpa only [semanticBadZ, dif_neg h14, if_pos heq, hcs] using h.2)]
              exact mul_nonneg (by norm_num) hq
          | some cs =>
              apply le_trans _ (etaCandidates_semChal_mass P.statement (baseRoundsZ P.rounds)
                (fun t => originalTotal P.statement.pub B t (fun j => cs.getD j.val 0))
                claim (maskTotal maskClaims))
              apply mean_mono
              intro s
              apply indicator_mono
              intro h
              simpa only [semanticBadZ, dif_neg h14, if_pos heq, hcs] using h.2
    · rw [if_neg heq, if_pos hi]
      have h15 : 15 ≤ P.rounds.length := by omega
      by_cases hd : degreeOK (unmaskSem sm)
      swap
      · rw [hz (fun _ h => hd (h.1 h15))]
        have hδ := deltaQ_nonneg
        positivity
      cases hcs : semChalsZ P.rounds with
      | none =>
          rw [hz (by intro c h; simpa only [semanticBadZ, dif_neg h14, if_neg heq, dif_pos hi, hcs] using h.2)]
          have hδ := deltaQ_nonneg
          positivity
      | some cs =>
          cases hc : claimOf P.rounds with
          | none =>
              rw [hz (by intro c h; simpa only [semanticBadZ, dif_neg h14, if_neg heq, dif_pos hi, hcs, hc] using h.2)]
              have hδ := deltaQ_nonneg
              positivity
          | some claim =>
              let ts := candidates P.statement (baseRoundsZ P.rounds) .none
              let G := fun t => virtualPolyZ maskClaims P.statement.pub B t
                (fun j => cs.getD j.val 0) (cs.getD 14 0)
              let j : Fin 10 := ⟨P.rounds.length - 15, by omega⟩
              let pref : Fin j.val → SemE := fun k => cs.getD (15 + k.val) 0
              calc
                _ ≤ mean (fun s : State => indicator
                    (alphaSomeBad ts G (currentPolyZ sm) j pref (semChal s))) := by
                  apply mean_mono
                  intro s
                  apply indicator_mono
                  intro h
                  simpa only [semanticBadZ, dif_neg h14, if_neg heq, dif_pos hi, hcs, hc] using h.2
                _ ≤ (ts.card * 27 : Nat) * ((1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4) :=
                  alphaSomeBad_semChal_mass ts G (currentPolyZ sm) (currentPolyZ_degree sm hd) j pref
                _ ≤ 2700 * ((1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4) := by
                  apply mul_le_mul_of_nonneg_right _ hq
                  exact_mod_cast (show ts.card * 27 ≤ 2700 by
                    have h := candidates_card P.statement (baseRoundsZ P.rounds) .none
                    change ts.card ≤ 100 at h
                    omega)
                _ = (1 + deltaQ) * (2700 / (AspisCircleGroupOrder.P : ℚ)^4) := by ring

#print axioms semantic_round_densityZ
end
end R0P.Mask
