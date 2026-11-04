import QueryScanExhaustion
import R0Z.HvzkS

/-! QueryScan's independent-word counting bound, sharpened before taking the
union over eight real and eight simulator attempts. Source/history transport
is deliberately a field of ScanCoupling, not inferred from classical ROM. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanPrivacyFinal
open R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable

abbrev scanProbability : ℚ := AspisR1.QueryScanExhaustion.probability (2^18) 64 21

theorem scan_probability_le : scanProbability ≤ 1 / (2 : ℚ)^486 := by
  have h := AspisR1.QueryScanExhaustion.probability_le
    (N := 2^18) (n := 64) (k := 21) (by positivity)
  have h21 : (21 : ℚ)^4 ≤ (2 : ℚ)^18 := by norm_num
  have hn : ((2 : ℚ)^18)^21 * (21 : ℚ)^64 ≤ (2 : ℚ)^666 := by
    calc _ = ((2 : ℚ)^18)^21 * ((21 : ℚ)^4)^16 := by rw [← pow_mul (21 : ℚ) 4 16]
         _ ≤ ((2 : ℚ)^18)^21 * ((2 : ℚ)^18)^16 := by gcongr
         _ = (2 : ℚ)^666 := by rw [← pow_mul, ← pow_mul, ← pow_add]
  have hc : ((2^18 : ℕ) : ℚ) = (2 : ℚ)^18 := by norm_cast
  rw [hc] at h
  calc _ ≤ (2 : ℚ)^666 / ((2 : ℚ)^18)^64 :=
          h.trans (div_le_div_of_nonneg_right hn (by positivity))
       _ = 1 / (2 : ℚ)^486 := by
          rw [← pow_mul, show 18*64 = 666+486 from rfl, pow_add]
          field_simp

/-- Each scan event is charged on a common finite coupling space. The mass
premise must hold for the actual reached histories, including repeated reads.
Agreement names the whole observation, so includes retry/failure publication.
No independence among the eight events is required. -/
structure ScanCoupling {R M : Type} [Fintype R] [Fintype M]
    (source : R → ℚ) (model : M → ℚ) where
  cp : Coupling R M
  queryScan : Fin 8 → cp.S → Prop
  R_rom_query_word_history : ∀ i, eventMass (queryScan i) ≤ scanProbability
  R_wire_agreement_off_queryScan : ∀ s, ¬ (∃ i, queryScan i s) →
    source (cp.toR s) = model (cp.toM s)

theorem scan_coupling_le {R M : Type} [Fintype R] [Fintype M]
    (f : R → ℚ) (g : M → ℚ) (c : ScanCoupling f g)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    |mean f - mean g| ≤ 8 / (2 : ℚ)^486 := by
  have hu : eventMass (fun s => ∃ i, c.queryScan i s) ≤
      ∑ i : Fin 8, eventMass (c.queryScan i) := by
    unfold eventMass
    rw [← mean_sum Finset.univ]
    apply mean_le_mean
    intro s
    by_cases he : ∃ i, c.queryScan i s
    · obtain ⟨i, hi⟩ := he
      rw [if_pos ⟨i, hi⟩]
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin 8 => if c.queryScan j s then (1 : ℚ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [if_pos hi] using h
    · rw [if_neg he]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have hs : (∑ i : Fin 8, eventMass (c.queryScan i)) ≤ 8 / (2 : ℚ)^486 := by
    calc _ ≤ ∑ _i : Fin 8, 1 / (2 : ℚ)^486 :=
          Finset.sum_le_sum (fun i _ => (c.R_rom_query_word_history i).trans scan_probability_le)
         _ = _ := by simp [div_eq_mul_inv]
  rw [← c.cp.meanR f, ← c.cp.meanM g]
  exact (until_bad _ _ (fun s => hf _) (fun s => hg _) _
    c.R_wire_agreement_off_queryScan).trans (hu.trans hs)

/-- Both source handoffs together: 8 real + 8 ideal scans. -/
theorem query_error_le : (16 / (2 : ℚ)^486) ≤ 1 / (2 : ℚ)^454 := by
  rw [show (486 : ℕ) = 32 + 454 from rfl, pow_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h : (16 : ℚ) ≤ 2^32 := by norm_num
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (by positivity : (0 : ℚ) ≤ 2^454)

#print axioms scan_probability_le
#print axioms scan_coupling_le
#print axioms query_error_le
end R1Z.QueryScanPrivacyFinal
