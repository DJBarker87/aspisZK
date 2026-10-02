import AspisV8R19.R411EqualLegalQueryMass
import AspisV8R19.R412LegalQueryEnumeration

/-! The bounded independent-answer q22 kernel has a uniform successful
marginal, multiplied by its actual success mass. Failure is not conditioned
away; no law for the shared source oracle or publication is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R417Q22SuccessLaw
open R407Q22CandidateKernel R411EqualLegalQueryMass R412LegalQueryEnumeration
open OracleResampling Q22WordScan Q22SamplerInvariants
noncomputable section
open scoped BigOperators

theorem mean_sum {X Y : Type} [Fintype X] [Fintype Y] (f : Y → X → ℚ) :
    mean (fun x => ∑ y, f y x) = ∑ y, mean (f y) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem mean_scale {X : Type} [Fintype X] (f : X → ℚ) (c : ℚ) :
    mean (fun x => f x*c) = mean f*c := by
  simp only [mean, ← Finset.sum_mul]
  ring

theorem kernel_sum {Y : Type} [Fintype Y] (n : Nat) (q : ScanState)
    (f : Y → Except Nat (List Nat) → ℚ) :
    candidateKernel n q (fun r => ∑ y, f y r) = ∑ y, candidateKernel n q (f y) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [candidateKernel, if_pos hd]
        rw [← mean_sum]
        apply mean_congr
        intro a
        split_ifs with hs
        · rfl
        · exact ih _
      · simp only [candidateKernel, if_neg hd]

theorem kernel_scale (n : Nat) (q : ScanState)
    (f : Except Nat (List Nat) → ℚ) (c : ℚ) :
    candidateKernel n q (fun r => f r*c) = candidateKernel n q f*c := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [candidateKernel, if_pos hd]
        rw [← mean_scale]
        apply mean_congr
        intro a
        split_ifs with hs
        · rfl
        · exact ih _
      · simp only [candidateKernel, if_neg hd]

theorem kernel_congr_valid (n : Nat) (q : ScanState) (hq : Valid q)
    (f g : Except Nat (List Nat) → ℚ)
    (heq : ∀ r, ResultValid r → f r = g r) :
    candidateKernel n q f = candidateKernel n q g := by
  induction n generalizing q with
  | zero => exact heq _ (finish_valid q hq)
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [candidateKernel, if_pos hd]
        apply mean_congr
        intro a
        have hv : Valid (scan q (List.ofFn (fun j => (a j).val))).1 := by
          apply scan_valid q _ hq
          intro x hx
          rcases List.mem_ofFn.mp hx with ⟨j, rfl⟩
          exact (a j).isLt
        split_ifs with hs
        · exact heq _ (finish_valid _ hv)
        · exact ih _ hv
      · simpa only [candidateKernel, if_neg hd] using heq _ (finish_valid q hq)

set_option linter.constructorNameAsVariable false in
theorem kernel_expansion (n : Nat) (test : Except Nat (List Nat) → ℚ)
    (herr : ∀ k, test (.error k) = 0) :
    candidateKernel n ⟨[],0⟩ test =
      ∑ u : LegalQuery, atomMass n (enumQuery u)*test (.ok (enumQuery u)) := by
  classical
  rw [kernel_congr_valid n ⟨[],0⟩ (by simp [Valid]) test
    (fun r => ∑ u : LegalQuery, if r = .ok (enumQuery u) then test (.ok (enumQuery u)) else 0)
    (fun r hr => test_eq_legal_sum r hr test herr), kernel_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hf : (fun r : Except Nat (List Nat) =>
      if r = .ok (enumQuery u) then test (.ok (enumQuery u)) else 0) =
      (fun r => (if r = .ok (enumQuery u) then (1 : ℚ) else 0)*test (.ok (enumQuery u))) := by
    funext r
    split_ifs <;> simp
  rw [hf, kernel_scale]
  rfl

def successMass (n : Nat) : ℚ := candidateKernel n ⟨[],0⟩
  (fun r => match r with | .ok _ => 1 | .error _ => 0)

theorem success_mass_atom (n : Nat) (u : LegalQuery) :
    successMass n = atomMass n (enumQuery u)*(Fintype.card LegalQuery : ℚ) := by
  rw [successMass, kernel_expansion n _ (by intro k; rfl)]
  have heq : ∀ v : LegalQuery, atomMass n (enumQuery v) = atomMass n (enumQuery u) := by
    intro v
    exact equal_legal_atom_mass n v.1 u.1 v.2 u.2
  simp only [heq, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem uniform_success (n : Nat) (u : LegalQuery)
    (test : Except Nat (List Nat) → ℚ) (herr : ∀ k, test (.error k) = 0) :
    candidateKernel n ⟨[],0⟩ test =
      successMass n * mean (fun v : LegalQuery => test (.ok (enumQuery v))) := by
  letI : Nonempty LegalQuery := ⟨u⟩
  have hc : (Fintype.card LegalQuery : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos))
  rw [kernel_expansion n test herr, success_mass_atom n u, mean]
  have heq : ∀ v : LegalQuery, atomMass n (enumQuery v) = atomMass n (enumQuery u) := by
    intro v
    exact equal_legal_atom_mass n v.1 u.1 v.2 u.2
  simp only [heq, ← Finset.mul_sum]
  field_simp

#print axioms mean_sum
#print axioms mean_scale
#print axioms kernel_sum
#print axioms kernel_scale
#print axioms kernel_congr_valid
#print axioms kernel_expansion
#print axioms success_mass_atom
#print axioms uniform_success
end
end AspisV8R19.R417Q22SuccessLaw
