import FS.LemmaA
import AspisV8R19.CausalFirstHitUnionBound

set_option autoImplicit false
noncomputable section

namespace AspisR1.RandomizedExtractorFixedLogComposition

open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

variable {L C W : Type} [Fintype L] [Nonempty L] [Fintype C] [Nonempty C]

/-- Failure includes rejection and any returned value that is not a witness.
The coin space is sampled independently after the completed log. -/
def badOutput (accept : L → Prop) (relation : L → W → Prop)
    (extract : L → C → Option W) (log : L) (coins : C) : Prop :=
  accept log ∧
    (extract log coins = none ∨
      ∃ w, extract log coins = some w ∧ ¬ relation log w)

/-- A per-completed-log Las Vegas guarantee composes with any existing
protocol bad-event bound. The only extractor randomness is the independent
finite coin space `C`; no pointwise D1 premise is imposed on the randomized
extractor. `complete` says that on a good completed log every non-aborted
execution returns a relation witness. -/
theorem accepted_badOutput_le_protocolBad_add_fixedLogAbort
    (accept good : L → Prop) (relation : L → W → Prop)
    (extract : L → C → Option W) (bankAbort : L → C → Prop)
    (protocolBound δE : ℚ)
    (hprotocol : mean (fun log => indicator (accept log ∧ ¬ good log)) ≤ protocolBound)
    (habort : ∀ log, mean (fun coins => indicator (bankAbort log coins)) ≤ δE)
    (hδ : 0 ≤ δE)
    (hcomplete : ∀ log coins, good log → ¬ bankAbort log coins →
      ∃ w, extract log coins = some w ∧ relation log w) :
    mean (fun lc : L × C =>
      indicator (badOutput accept relation extract lc.1 lc.2)) ≤
        protocolBound + δE := by
  have hsubset : ∀ log coins,
      badOutput accept relation extract log coins →
        (accept log ∧ ¬ good log) ∨ (good log ∧ bankAbort log coins) := by
    intro log coins hfail
    rcases hfail with ⟨ha, hfail⟩
    by_cases hg : good log
    · rcases hfail with hnone | ⟨w, hout, hbad⟩
      · right
        have hab : bankAbort log coins := by
          by_contra hab
          obtain ⟨w, hw, _⟩ := hcomplete log coins hg hab
          rw [hnone] at hw
          cases hw
        exact ⟨hg, hab⟩
      · have hab : bankAbort log coins := by
          by_contra hab
          obtain ⟨w', hw', hrel'⟩ := hcomplete log coins hg hab
          rw [hout] at hw'
          have heq : w = w' := Option.some.inj hw'
          subst w'
          exact hbad hrel'
        exact Or.inr ⟨hg, hab⟩
    · exact Or.inl ⟨ha, hg⟩
  have hpoint : ∀ lc : L × C,
      indicator (badOutput accept relation extract lc.1 lc.2) ≤
        indicator (accept lc.1 ∧ ¬ good lc.1) +
          indicator (good lc.1 ∧ bankAbort lc.1 lc.2) := by
    intro lc
    calc
      indicator (badOutput accept relation extract lc.1 lc.2) ≤
          indicator ((accept lc.1 ∧ ¬ good lc.1) ∨
            (good lc.1 ∧ bankAbort lc.1 lc.2)) :=
              FS.indicator_mono (hsubset lc.1 lc.2)
      _ ≤ indicator (accept lc.1 ∧ ¬ good lc.1) +
          indicator (good lc.1 ∧ bankAbort lc.1 lc.2) := FS.indicator_or_le _ _
  have hbadProduct : mean (fun lc : L × C =>
      indicator (accept lc.1 ∧ ¬ good lc.1)) =
      mean (fun log => indicator (accept log ∧ ¬ good log)) := by
    calc
      mean (fun lc : L × C => indicator (accept lc.1 ∧ ¬ good lc.1)) =
          mean (fun log => mean (fun _ : C => indicator (accept log ∧ ¬ good log))) := by
            exact AspisV8R19.OracleResampling.mean_prod
              (X := L) (Y := C) (fun log _ => indicator (accept log ∧ ¬ good log))
      _ = mean (fun log => indicator (accept log ∧ ¬ good log)) := by
            apply mean_congr
            intro log
            rw [mean_const]
  have habortProduct : mean (fun lc : L × C =>
      indicator (good lc.1 ∧ bankAbort lc.1 lc.2)) ≤ δE := by
    calc
      mean (fun lc : L × C => indicator (good lc.1 ∧ bankAbort lc.1 lc.2)) =
          mean (fun log => mean (fun coins => indicator (good log ∧ bankAbort log coins))) :=
            AspisV8R19.OracleResampling.mean_prod
              (X := L) (Y := C) (fun log coins => indicator (good log ∧ bankAbort log coins))
      _ ≤ mean (fun _ : L => δE) := by
            apply FS.mean_mono
            intro log
            by_cases hg : good log
            · calc
                mean (fun coins => indicator (good log ∧ bankAbort log coins)) =
                    mean (fun coins => indicator (bankAbort log coins)) := by
                      apply mean_congr
                      intro coins
                      simp [hg]
                _ ≤ δE := habort log
            · calc
                mean (fun coins => indicator (good log ∧ bankAbort log coins)) = 0 := by
                  calc
                    mean (fun coins => indicator (good log ∧ bankAbort log coins)) =
                        mean (fun _ : C => 0) := by
                          apply mean_congr
                          intro coins
                          simp [hg, indicator]
                    _ = 0 := by rw [mean_const]
                _ ≤ δE := hδ
      _ = δE := mean_const _
  calc
    mean (fun lc : L × C =>
        indicator (badOutput accept relation extract lc.1 lc.2)) ≤
      mean (fun lc : L × C =>
        indicator (accept lc.1 ∧ ¬ good lc.1) +
          indicator (good lc.1 ∧ bankAbort lc.1 lc.2)) := by
            apply FS.mean_mono
            exact hpoint
    _ = mean (fun lc : L × C => indicator (accept lc.1 ∧ ¬ good lc.1)) +
          mean (fun lc : L × C => indicator (good lc.1 ∧ bankAbort lc.1 lc.2)) :=
            FS.mean_add _ _
    _ ≤ protocolBound + δE := by
      rw [hbadProduct]
      exact add_le_add hprotocol habortProduct

end AspisR1.RandomizedExtractorFixedLogComposition
end
