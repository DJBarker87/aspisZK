import AspisR1BatchedActualReducerFinish
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas.Std

namespace AspisR1BatchedAllPrefix

open AspisR1BatchedFoldSourceStep

abbrev cap : Nat := (2 ^ 31 - 2) ^ 2
abbrev Usize := UScalar UScalarTy.Usize

def run (terms raw : Nat) : List Nat → Nat
  | [] => raw
  | p :: ps => run (terms + 1) (sourcePush terms raw p) ps

def sumProducts : List Nat → Nat
  | [] => 0
  | p :: ps => p + sumProducts ps

def CounterTrace : Nat → List Usize → Prop
  | _, [] => True
  | t, c :: cs =>
      c.val = t ∧ ∃ next : Usize,
        UScalar.add c (1#usize) = .ok next ∧ next.val = t + 1 ∧
        CounterTrace (t + 1) cs

def runActual : List Usize → List Nat → Nat → Nat
  | c :: cs, p :: ps, raw =>
      runActual cs ps (AspisR1BatchedActualCounter.actualSourcePush c raw p)
  | _, _, raw => raw

/-- The executable Usize counter/mask path is exactly the Nat cadence model
whenever each source checked increment succeeds and advances by one. -/
theorem runActual_eq_run (counters : List Usize) (products : List Nat)
    (raw start : Nat) (hlen : counters.length = products.length)
    (htrace : CounterTrace start counters) :
    runActual counters products raw = run start raw products := by
  induction counters generalizing products raw start with
  | nil =>
      cases products with
      | nil => rfl
      | cons p ps => simp at hlen
  | cons c cs ih =>
      cases products with
      | nil => simp at hlen
      | cons p ps =>
          rcases htrace with ⟨hc, next, hnext, hval, htail⟩
          have hlen' : cs.length = ps.length := by simp at hlen; omega
          simp only [runActual, run]
          rw [AspisR1BatchedActualCounter.actualSourcePush_eq, hc]
          exact ih ps (sourcePush start raw p)
            (start + 1) hlen' htail

theorem pending_bound (terms raw : Nat) (ht : terms % 4 = 0)
    (hr : raw < 2 ^ 34) : raw < 2 ^ 34 + (terms % 4) * cap := by
  simpa [ht] using hr

/-- Every stream prefix obeys the source's flush cadence.  With `k` pending
terms after the most recent fold, the raw lane is below `2^34 + k*cap`; hence
all four pre-fold additions fit `u64`, and each flush returns to `<2^34`. -/
theorem run_invariant (products : List Nat)
    (hproducts : ∀ p ∈ products, p ≤ cap) :
    ∀ terms raw, raw < 2 ^ 34 + (terms % 4) * cap →
      run terms raw products < 2 ^ 34 + ((terms + products.length) % 4) * cap ∧
      run terms raw products % modulus = (raw + sumProducts products) % modulus := by
  induction products with
  | nil =>
      intro terms raw hr
      simpa [run, sumProducts] using And.intro hr (rfl : raw % modulus = (raw + 0) % modulus)
  | cons p ps ih =>
      intro terms raw hr
      have hp : p ≤ cap := hproducts p (by simp)
      have htail : ∀ q ∈ ps, q ≤ cap := by
        intro q hq
        exact hproducts q (by simp [hq])
      by_cases hflush : terms % 4 = 3
      · have hsum64 : raw + p < 2 ^ 64 := by
          have hcap : cap = 4611686009837453316 := by norm_num [cap]
          rw [hcap] at hr hp
          have hmod3 : terms % 4 = 3 := hflush
          omega
        have hfold : fold (raw + p) < 2 ^ 34 := fold_lt_two34 hsum64
        have hres : sourcePush terms raw p % modulus = (raw + p) % modulus :=
          sourcePush_mod terms raw p
        have hbound : fold (raw + p) <
            2 ^ 34 + ((terms + 1) % 4) * cap := by
          have hnext : (terms + 1) % 4 = 0 := by omega
          rw [hnext]
          exact hfold
        have hpush : sourcePush terms raw p = fold (raw + p) := by
          simp only [sourcePush, if_pos hflush]
        have hrest := ih htail (terms + 1) (fold (raw + p)) hbound
        constructor
        · change run (terms + 1) (sourcePush terms raw p) ps <
              2 ^ 34 + ((terms + (p :: ps).length) % 4) * cap
          rw [hpush]
          have hidx : (terms + 1 + ps.length) % 4 =
              (terms + (p :: ps).length) % 4 := by
            simp only [List.length_cons]
            omega
          rw [← hidx]
          exact hrest.1
        · change run (terms + 1) (sourcePush terms raw p) ps % modulus =
              (raw + (p + sumProducts ps)) % modulus
          have htailres := hrest.2
          rw [hpush]
          calc
            run (terms + 1) (fold (raw + p)) ps % modulus =
                (fold (raw + p) + sumProducts ps) % modulus := by simpa using htailres
            _ = (raw + p + sumProducts ps) % modulus := by
              simp only [Nat.add_mod, Nat.mod_mod, fold_preserves_mod]
            _ = (raw + (p + sumProducts ps)) % modulus :=
              congrArg (fun z => z % modulus) (Nat.add_assoc raw p (sumProducts ps))
      · have hnot3 : terms % 4 < 3 := by omega
        have hnext : (terms + 1) % 4 = terms % 4 + 1 := by omega
        have hcap : cap = 4611686009837453316 := by norm_num [cap]
        have hk : terms % 4 = 0 ∨ terms % 4 = 1 ∨ terms % 4 = 2 := by omega
        have hraw' : raw + p < 2 ^ 34 + ((terms + 1) % 4) * cap := by
          rcases hk with hk | hk | hk
          · have hnext' : (terms + 1) % 4 = 1 := by rw [hnext, hk]
            rw [hnext']
            rw [hcap, hk] at hr
            rw [hcap] at hp
            norm_num at hr hp
            omega
          · have hnext' : (terms + 1) % 4 = 2 := by rw [hnext, hk]
            rw [hnext']
            rw [hcap, hk] at hr
            rw [hcap] at hp
            norm_num at hr hp
            omega
          · have hnext' : (terms + 1) % 4 = 3 := by rw [hnext, hk]
            rw [hnext']
            rw [hcap, hk] at hr
            rw [hcap] at hp
            norm_num at hr hp
            omega
        have hres : sourcePush terms raw p % modulus = (raw + p) % modulus :=
          sourcePush_mod terms raw p
        have hpush : sourcePush terms raw p = raw + p := by
          simp only [sourcePush, if_neg hflush]
        have hrest := ih htail (terms + 1) (raw + p) hraw'
        constructor
        · change run (terms + 1) (sourcePush terms raw p) ps <
              2 ^ 34 + ((terms + (p :: ps).length) % 4) * cap
          rw [hpush]
          have hidx : (terms + 1 + ps.length) % 4 =
              (terms + (p :: ps).length) % 4 := by
            simp only [List.length_cons]
            omega
          rw [← hidx]
          exact hrest.1
        · change run (terms + 1) (sourcePush terms raw p) ps % modulus =
              (raw + (p + sumProducts ps)) % modulus
          have htailres := hrest.2
          rw [hpush]
          calc
            run (terms + 1) (raw + p) ps % modulus =
                (raw + p + sumProducts ps) % modulus := by simpa using htailres
            _ = (raw + (p + sumProducts ps)) % modulus := by
              exact congrArg (fun z => z % modulus) (Nat.add_assoc raw p (sumProducts ps))

/-- Any actual counter trace's output has the all-prefix bound and residue
proved above, provided every actual product is a product of canonical limbs. -/
theorem actual_run_invariant (counters : List Usize) (products : List Nat)
    (raw start : Nat) (hlen : counters.length = products.length)
    (htrace : CounterTrace start counters)
    (hproducts : ∀ p ∈ products, p ≤ cap)
    (hraw : raw < 2 ^ 34 + (start % 4) * cap) :
    runActual counters products raw <
        2 ^ 34 + ((start + products.length) % 4) * cap ∧
      runActual counters products raw % modulus =
        (raw + sumProducts products) % modulus := by
  rw [runActual_eq_run counters products raw start hlen htrace]
  exact run_invariant products hproducts start raw hraw

/-- Starting at a group boundary, each `value()` reduction is applied to a
bounded raw lane and returns the canonical residue after any stream prefix. -/
theorem start_boundary (products : List Nat)
    (hproducts : ∀ p ∈ products, p ≤ cap)
    (raw : Nat) (hr : raw < 2 ^ 34) :
    run 0 raw products < 2 ^ 34 + (products.length % 4) * cap ∧
    run 0 raw products % modulus = (raw + sumProducts products) % modulus := by
  have h := run_invariant products hproducts 0 raw (by simpa using hr)
  simpa using h

theorem start_boundary_u64 (products : List Nat)
    (hproducts : ∀ p ∈ products, p ≤ cap)
    (raw : Nat) (hr : raw < 2 ^ 34) : run 0 raw products < 2 ^ 64 := by
  have hi := (start_boundary products hproducts raw hr).1
  have hcap : cap = 4611686009837453316 := by norm_num [cap]
  have hk : products.length % 4 = 0 ∨ products.length % 4 = 1 ∨
    products.length % 4 = 2 ∨ products.length % 4 = 3 := by omega
  rcases hk with hk | hk | hk | hk
  · rw [hk] at hi; norm_num [cap] at hi; omega
  · rw [hk] at hi; norm_num [cap] at hi; omega
  · rw [hk] at hi; norm_num [cap] at hi; omega
  · rw [hk] at hi; norm_num [cap] at hi; omega

/-- Applying the retained reducer after any stream prefix returns the exact
canonical field residue; the pending one-to-three products are included. -/
theorem value_after_any_prefix (products : List Nat)
    (hproducts : ∀ p ∈ products, p ≤ cap)
    (raw : Nat) (hr : raw < 2 ^ 34) :
    ∃ z : AspisR1Qm31ArithmeticProbe.field.M31,
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
        (Aeneas.Std.UScalar.ofNatCore (run 0 raw products)
          (start_boundary_u64 products hproducts raw hr)) = .ok z ∧
      z.val = (raw + sumProducts products) % modulus ∧ z.val < modulus := by
  have hinv := start_boundary products hproducts raw hr
  have hacc : run 0 raw products < 2 ^ UScalarTy.U64.numBits := by
    rw [UScalarTy.U64_numBits_eq]
    exact start_boundary_u64 products hproducts raw hr
  obtain ⟨z, hz, hmod, hcanonical⟩ :=
    AspisR1.ExtractedCurrentReducer.current_wrapper_mod
      (Aeneas.Std.UScalar.ofNatCore (run 0 raw products)
        hacc)
  have hvalue : (Aeneas.Std.UScalar.ofNatCore (run 0 raw products)
      hacc).val = run 0 raw products := rfl
  rw [hvalue] at hmod
  refine ⟨z, hz, ?_, ?_⟩
  · simpa [modulus, AspisR1BatchedFoldArithmetic.modulus] using hmod.trans hinv.2
  · simpa [modulus, AspisR1BatchedFoldArithmetic.modulus] using hcanonical

#print axioms value_after_any_prefix
#print axioms start_boundary_u64
#print axioms runActual_eq_run
#print axioms actual_run_invariant

#print axioms run_invariant
#print axioms start_boundary

end AspisR1BatchedAllPrefix
