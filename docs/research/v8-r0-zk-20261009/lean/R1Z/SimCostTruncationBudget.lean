import R1Z.SimCostSampling

/-! Deterministic multi-sample truncation cost and explicit error arithmetic.
The statistical budget below is for the independent-word geometric model of
SimCostSampling; no source coupling or simulator sample-count certificate is
inferred from it. In particular it is not a new privacy theorem. -/
set_option autoImplicit false
namespace R1Z.SimCostTruncationBudget
open R1Z.SimCostWriter R1Z.SimCostSampling

/-- Each stream supplies at most B rejection trials. None is an explicit
failure result; no exact-uniform fallback is silently substituted. -/
def batch {A : Type} : List (List (Option A)) → Costed (List (Option A))
  | [] => ([],0)
  | xs :: rest =>
    let s := truncate xs
    let t := batch rest
    (s.1 :: t.1, s.2+t.2)

theorem batch_erase {A : Type} (streams : List (List (Option A))) :
    (batch streams).1 = streams.map reference := by
  induction streams with
  | nil => rfl
  | cons xs rest ih => simp only [batch, List.map_cons, truncate_erase, ih]

theorem batch_bound {A : Type} (B : Nat) (streams : List (List (Option A)))
    (hs : ∀ xs ∈ streams, xs.length ≤ B) :
    (batch streams).2 ≤ B * streams.length := by
  induction streams with
  | nil => simp only [batch, List.length_nil, Nat.mul_zero, le_refl]
  | cons xs rest ih =>
    have hxs := (truncate_bound xs).trans (hs xs List.mem_cons_self)
    have hrest := ih (fun ys hy => hs ys (List.mem_cons_of_mem xs hy))
    simp only [batch, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Union-budget expression. Use it as a failure-mass upper bound only after
proving the corresponding per-sample rejection law for the actual source. -/
def extraMass (samples : Nat) : ℚ := (samples : ℚ) * m31Reject^8

theorem extra_mass_exact (samples : Nat) :
    extraMass samples = (samples : ℚ) / (2 : ℚ)^248 := by
  rw [extraMass, m31_tail]
  norm_num only [Nat.reduceMul]
  ring

theorem extra_mass_nonneg (samples : Nat) : 0 ≤ extraMass samples := by
  rw [extra_mass_exact]
  positivity

/-- A deliberately generous numerical envelope, not a claim that the
simulator has been certified to use at most this many samples. -/
theorem extra_mass_small (samples : Nat) (hs : samples ≤ 2^128) :
    extraMass samples ≤ 1 / (2 : ℚ)^120 := by
  have hc : (samples : ℚ) ≤ (2 : ℚ)^128 := by exact_mod_cast hs
  rw [extra_mass_exact]
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans (by norm_num)

/-- The existing published numeric envelope at honest-call count ≤2^25,
plus the extra truncation budget, still has substantial slack below 2^-100.
Both envelope and actual failure-law premises must be supplied by an endpoint. -/
theorem total_below_target (epsilon : ℚ)
    (he : epsilon ≤ 1/(2:ℚ)^109 + 1/(2:ℚ)^137 + 1/(2:ℚ)^454 +
      128*((2:ℚ)^25+1)/(2:ℚ)^190)
    (samples : Nat) (hs : samples ≤ 2^128) :
    epsilon + extraMass samples < 1/(2:ℚ)^100 := by
  have ht := extra_mass_small samples hs
  have hp : (2:ℚ)^137 ≤ (2:ℚ)^454 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^137 :=
    one_div_le_one_div_of_le (by positivity) hp
  have hn : 1/(2:ℚ)^109 + 1/(2:ℚ)^137 + 1/(2:ℚ)^137 +
      128*((2:ℚ)^25+1)/(2:ℚ)^190 + 1/(2:ℚ)^120 < 1/(2:ℚ)^100 := by norm_num
  have hb : epsilon + extraMass samples ≤
      1/(2:ℚ)^109 + 1/(2:ℚ)^137 + 1/(2:ℚ)^137 +
      128*((2:ℚ)^25+1)/(2:ℚ)^190 + 1/(2:ℚ)^120 := by
    linarith
  exact lt_of_le_of_lt hb hn

/-- The geometric expected-draw envelope for n samples; independence is needed
within each sampler to justify expectedDraws, not across separate samplers
when adding expectations. -/
theorem batch_expected_bound (samples B : Nat) :
    (samples : ℚ) * expectedDraws m31Reject B ≤ 2 * samples := by
  have ht := m31_expected B
  have hn : (0 : ℚ) ≤ samples := Nat.cast_nonneg _
  nlinarith

#print axioms batch_erase
#print axioms batch_bound
#print axioms extra_mass_exact
#print axioms extra_mass_nonneg
#print axioms extra_mass_small
#print axioms total_below_target
#print axioms batch_expected_bound
end R1Z.SimCostTruncationBudget
