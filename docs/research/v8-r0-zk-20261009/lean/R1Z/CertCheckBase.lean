import R1Z.CertCheckExtracted
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! D49.4 C3: plumbing for the extracted P_R1 checker (`R1CertCheck`, Aeneas b59d5188).

Only the success direction is used: every lemma reads `f … = ok r` forward.
`gs s k` is the M31 value of slice entry `k`.  `flag_loop` and `acc_loop` are
the two loop shapes of the checker (a Boolean flag cleared on a failed test,
and a u64 accumulator); each extracted loop instantiates one of them by a
one-step lemma, so no loop is ever unfolded on concrete sizes. -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck
open scoped BigOperators

/-- The M31 modulus and field. -/
abbrev PN : ℕ := 2147483647
abbrev ZP := ZMod PN

/-- The M31 value of a slice entry. -/
def gs (s : Slice U32) (k : ℕ) : ZP := ((s.val[k]!).val : ZP)

/-! ### Result plumbing -/

theorem bind_eq_ok {α β : Type} {x : Result α} {f : α → Result β} {r : β}
    (h : Bind.bind x f = ok r) : ∃ v, x = ok v ∧ f v = ok r := by
  cases x with
  | ok v => exact ⟨v, rfl, by simpa [Bind.bind] using h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem ok_inj {α : Type} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by
  cases h; rfl

theorem add_ok {ty : UScalarTy} {x y z : UScalar ty} (h : x + y = ok z) :
    z.val = x.val + y.val := by
  have e := UScalar.add_equiv x y
  rw [h] at e
  exact e.2.1

theorem mul_ok {ty : UScalarTy} {x y z : UScalar ty} (h : x * y = ok z) :
    z.val = x.val * y.val := by
  have e := UScalar.mul_equiv x y
  have h' : UScalar.mul x y = ok z := h
  rw [h'] at e
  exact e.2.1

theorem sub_ok {ty : UScalarTy} {x y z : UScalar ty} (h : x - y = ok z) :
    z.val = x.val - y.val ∧ y.val ≤ x.val := by
  have e := UScalar.sub_equiv x y
  rw [h] at e
  obtain ⟨h1, h2, -⟩ := e
  constructor <;> omega

theorem rem_ok {ty : UScalarTy} {x y z : UScalar ty} (hy : y.val ≠ 0) (h : x % y = ok z) :
    z.val = x.val % y.val := by
  obtain ⟨z', hz', hv⟩ := WP.spec_imp_exists (UScalar.rem_spec x hy)
  rw [h] at hz'
  cases hz'
  exact hv

theorem div_ok {ty : UScalarTy} {x y z : UScalar ty} (hy : y.val ≠ 0) (h : x / y = ok z) :
    z.val = x.val / y.val := by
  obtain ⟨z', hz', hv⟩ := UScalar.div_spec x hy
  rw [h] at hz'
  cases hz'
  exact hv

theorem index_ok {v : Slice U32} {i : Usize} {x : U32} (h : Slice.index_usize v i = ok x) :
    i.val < v.val.length ∧ x = v.val[i.val]! := by
  unfold Slice.index_usize at h
  rw [Slice.getElem?_Usize_eq] at h
  cases hc : v.val[i.val]? with
  | none => rw [hc] at h; cases h
  | some y =>
    rw [hc] at h
    cases h
    refine ⟨(List.getElem?_eq_some_iff.1 hc).1, ?_⟩
    rw [List.getElem!_eq_getElem?_getD, hc]
    rfl

theorem cast64 (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.hBounds (by simp))

theorem castUs (x : U32) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt (lt_of_lt_of_le x.hBounds ?_)
  simp only [UScalarTy.U32_numBits_eq, UScalarTy.Usize_numBits_eq]
  exact Nat.pow_le_pow_right (by norm_num) System.Platform.le_numBits

theorem castUs64 (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt (lt_of_lt_of_le x.hBounds ?_)
  simp only [UScalarTy.U64_numBits_eq, UScalarTy.Usize_numBits_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by cases System.Platform.numBits_eq <;> simp_all)

theorem cast32 (x : U64) (h : x.val < 2 ^ 32) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

theorem P_val : P.val = PN := by
  unfold P
  rfl

theorem P_ne : P.val ≠ 0 := by rw [P_val]; norm_num

theorem modP_lt {x z : U64} (h : x % P = ok z) : z.val < PN ∧ (z.val : ZP) = (x.val : ZP) := by
  have e := rem_ok P_ne h
  rw [P_val] at e
  rw [e]
  exact ⟨Nat.mod_lt _ (by norm_num), ZMod.natCast_mod _ _⟩

theorem ne_false {α : Type} [BEq α] [LawfulBEq α] {x y : α} (h : (x != y) = false) : x = y := by
  simpa using h

/-! ### The two loop shapes -/

/-- A flag loop: the flag stays `true` only if every step's test holds. -/
theorem flag_loop {F : Bool → Usize → Result Bool} {n : ℕ} {Q : ℕ → Prop}
    (hstop : ∀ b i, ¬ i.val < n → F b i = ok b)
    (hstep : ∀ b i r, i.val < n → F b i = ok r →
      ∃ b' i', i'.val = i.val + 1 ∧ F b' i' = ok r ∧ (b' = true → b = true ∧ Q i.val)) :
    ∀ k b i, i.val + k = n → F b i = ok true → b = true ∧ ∀ j, i.val ≤ j → j < n → Q j
  | 0, b, i, hk, h => by
      rw [hstop b i (by omega)] at h
      exact ⟨ok_inj h, fun j h1 h2 => by omega⟩
  | k + 1, b, i, hk, h => by
      obtain ⟨b', i', hi', h', hb⟩ := hstep b i true (by omega) h
      obtain ⟨hb', hall⟩ := flag_loop hstop hstep k b' i' (by omega) h'
      obtain ⟨hb0, hq⟩ := hb hb'
      refine ⟨hb0, fun j h1 h2 => ?_⟩
      by_cases e : j = i.val
      · subst e; exact hq
      · exact hall j (by omega) h2

/-- Entry form: a flag loop started at `true` and index 0. -/
theorem flag_loop0 {F : Bool → Usize → Result Bool} {n : ℕ} {Q : ℕ → Prop}
    (hstop : ∀ b i, ¬ i.val < n → F b i = ok b)
    (hstep : ∀ b i r, i.val < n → F b i = ok r →
      ∃ b' i', i'.val = i.val + 1 ∧ F b' i' = ok r ∧ (b' = true → b = true ∧ Q i.val))
    (h : F true 0#usize = ok true) : ∀ j, j < n → Q j := by
  have := flag_loop hstop hstep n true 0#usize (by simp) h
  exact fun j hj => this.2 j (by simp) hj

/-- An accumulator loop over `ZP`. -/
theorem acc_loop {F : U64 → Usize → Result U64} {n : ℕ} {T : ℕ → ZP}
    (hstop : ∀ a i, ¬ i.val < n → F a i = ok a)
    (hstep : ∀ a i r, i.val < n → F a i = ok r →
      ∃ a' i', i'.val = i.val + 1 ∧ F a' i' = ok r ∧ (a'.val : ZP) = (a.val : ZP) + T i.val) :
    ∀ k a i r, i.val + k = n → F a i = ok r →
      (r.val : ZP) = (a.val : ZP) + ∑ j ∈ Finset.Ico i.val n, T j
  | 0, a, i, r, hk, h => by
      rw [hstop a i (by omega)] at h
      rw [← ok_inj h, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero]
  | k + 1, a, i, r, hk, h => by
      obtain ⟨a', i', hi', h', ha⟩ := hstep a i r (by omega) h
      rw [acc_loop hstop hstep k a' i' r (by omega) h', ha, hi',
        Finset.sum_eq_sum_Ico_succ_bot (show i.val < n by omega), add_assoc]

theorem acc_loop0 {F : U64 → Usize → Result U64} {n : ℕ} {T : ℕ → ZP}
    (hstop : ∀ a i, ¬ i.val < n → F a i = ok a)
    (hstep : ∀ a i r, i.val < n → F a i = ok r →
      ∃ a' i', i'.val = i.val + 1 ∧ F a' i' = ok r ∧ (a'.val : ZP) = (a.val : ZP) + T i.val)
    {r : U64} (h : F 0#u64 0#usize = ok r) : (r.val : ZP) = ∑ j ∈ Finset.range n, T j := by
  have := acc_loop hstop hstep n 0#u64 0#usize r (by simp) h
  rw [this, Finset.range_eq_Ico]
  simp

#print axioms bind_eq_ok
#print axioms add_ok
#print axioms mul_ok
#print axioms sub_ok
#print axioms rem_ok
#print axioms div_ok
#print axioms index_ok
#print axioms cast64
#print axioms castUs
#print axioms castUs64
#print axioms cast32
#print axioms modP_lt
#print axioms flag_loop
#print axioms flag_loop0
#print axioms acc_loop
#print axioms acc_loop0

end R1Z.CertCheck
