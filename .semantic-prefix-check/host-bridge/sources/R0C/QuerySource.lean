import R0C.QueryCounting
import AspisV8R19.R417Q22SuccessLaw
import AspisV8R19.R413GuardedOracleDistance

/-! The retained bounded source sampler: successful containment has the
hypergeometric law times its actual success mass. Errors contribute zero.
Only independent-answer semantics is claimed, not a duplex decoder theorem. -/
set_option autoImplicit false
namespace R0C.QuerySource
open AspisV8R19 AspisV8R19.SourceDuplexStep
open OracleResampling CausalFirstHitUnionBound AdaptiveFirstReadLaw
open R407Q22CandidateKernel R417Q22SuccessLaw R412LegalQueryEnumeration
noncomputable section
attribute [local instance] Classical.propDecidable

def initialLegal : LegalQuery :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun j : Fin (2^18) => j.val) h)⟩

/-- On valid successful results, each natural already lies below 2^18. -/
def containsOnly (M : Finset (Fin (2^18))) : Except Nat (List Nat) → ℚ
  | .error _ => 0
  | .ok xs => indicator (∀ x ∈ xs, (⟨x % (2^18), Nat.mod_lt _ (by positivity)⟩ : Fin (2^18)) ∈ M)

theorem containsOnly_enum (M : Finset (Fin (2^18))) (u : LegalQuery) :
    containsOnly M (.ok (enumQuery u)) = indicator (∀ i, u.val i ∈ M) := by
  simp only [containsOnly]
  apply congrArg indicator
  apply propext
  constructor
  · intro h i
    have hi := h (u.val i).val (by exact List.mem_ofFn.mpr ⟨i, rfl⟩)
    simpa only [Nat.mod_eq_of_lt (u.val i).isLt] using hi
  · intro h x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simpa only [Nat.mod_eq_of_lt (u.val i).isLt] using h i

theorem successful_subset_exact (s : State) (M : Finset (Fin (2^18))) :
    independentMean (Q22SamplerProgram.challengeProgram s)
      (fun v => containsOnly M v.2.1) =
      successMass 8 * ((M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ)) := by
  have hcount := QueryCounting.subset_mean 22 M
  simp only [Fintype.card_fin] at hcount
  have he : mean (fun u : LegalQuery => containsOnly M (.ok (enumQuery u))) =
      (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) :=
    (mean_congr (containsOnly_enum M)).trans hcount
  exact (challenge_candidate_kernel s (containsOnly M)).trans
    ((uniform_success 8 initialLegal (containsOnly M) (by intro k; rfl)).trans
      (congrArg (fun t : ℚ => successMass 8 * t) he))

theorem kernel_le_one (n : Nat) (q : Q22WordScan.ScanState)
    (test : Except Nat (List Nat) → ℚ) (h : ∀ r, test r ≤ 1) :
    candidateKernel n q test ≤ 1 := by
  induction n generalizing q with
  | zero => exact h _
  | succ n ih =>
    simp only [candidateKernel]
    split_ifs with hd
    · calc
        _ ≤ mean (fun _ : Fin 8 → Fin (2^18) => (1 : ℚ)) := by
          apply R413GuardedOracleDistance.mean_mono
          intro a
          split_ifs
          · exact h _
          · exact ih _
        _ = 1 := mean_const _
    · exact h _

theorem successMass_le_one (n : Nat) : successMass n ≤ 1 := by
  apply kernel_le_one
  intro r
  cases r <;> norm_num

/-- No division by success probability: the unconditional successful-event
mass is at most the ideal ratio, even when exhaustion has positive mass. -/
theorem successful_subset_le (s : State) (M : Finset (Fin (2^18))) :
    independentMean (Q22SamplerProgram.challengeProgram s)
      (fun v => containsOnly M v.2.1) ≤
      (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  exact (successful_subset_exact s M).le.trans
    (mul_le_of_le_one_left (by positivity) (successMass_le_one 8))

#print axioms successful_subset_exact
#print axioms successMass_le_one
#print axioms successful_subset_le
end
end R0C.QuerySource
