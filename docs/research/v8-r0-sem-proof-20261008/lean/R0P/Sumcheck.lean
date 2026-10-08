import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Lead: generic sumcheck soundness at the function level.

A prover claims `c = Σ_{b ∈ {0,1}^n} G b`. Round i sends `polys i`, the
verifier checks `p(0)+p(1)` against the running claim, samples `α i`, and the
claim becomes `p(α i)`; the final check evaluates `G α`. If the claim is
false and the verifier accepts, some `α i` is a root of the nonzero
polynomial `polys i − honest i`, where the honest round polynomial is
determined by `α 0..i−1`. The hypercube sum is defined by recursion on `n`,
so no finite universe is enumerated. -/
set_option autoImplicit false
namespace R0P.Sumcheck
open Polynomial

variable {K : Type} [Field K]

/-- `Σ_{b ∈ {0,1}^n} G b`, by recursion on the leading coordinate. -/
def bsum : (n : Nat) → ((Fin n → K) → K) → K
  | 0, G => G (fun i => i.elim0)
  | n+1, G => bsum n (fun v => G (Fin.cons 0 v)) + bsum n (fun v => G (Fin.cons 1 v))

/-- Every round's honest polynomial exists with degree ≤ d, for every prefix. -/
def IndDeg (d : Nat) : (n : Nat) → ((Fin n → K) → K) → Prop
  | 0, _ => True
  | n+1, G => (∃ h : K[X], h.natDegree ≤ d ∧ ∀ x, h.eval x = bsum n (fun v => G (Fin.cons x v))) ∧
      ∀ x, IndDeg d n (fun v => G (Fin.cons x v))

/-- The verifier's checks for one transcript. -/
def accept (d : Nat) : (n : Nat) → ((Fin n → K) → K) → K → (Fin n → K[X]) → (Fin n → K) → Prop
  | 0, G, c, _, _ => G (fun i => i.elim0) = c
  | n+1, G, c, polys, α =>
      (polys 0).natDegree ≤ d ∧ (polys 0).eval 0 + (polys 0).eval 1 = c ∧
      accept d n (fun v => G (Fin.cons (α 0) v)) ((polys 0).eval (α 0)) (Fin.tail polys) (Fin.tail α)

/-- The bad event of the transcript: at some round the prover's polynomial
differs from the honest one (the hypercube partial sum at the prefix, of
degree ≤ d) and the round's challenge is a root of their difference. For a
fixed prefix this is a root set of one nonzero polynomial of degree ≤ d. -/
def badAlpha (d : Nat) : (n : Nat) → ((Fin n → K) → K) → (Fin n → K[X]) → (Fin n → K) → Prop
  | 0, _, _, _ => False
  | n+1, G, polys, α =>
      (∃ h : K[X], h.natDegree ≤ d ∧ (∀ x, h.eval x = bsum n (fun v => G (Fin.cons x v))) ∧
        polys 0 ≠ h ∧ (polys 0 - h).eval (α 0) = 0) ∨
      badAlpha d n (fun v => G (Fin.cons (α 0) v)) (Fin.tail polys) (Fin.tail α)

/-- Soundness: an accepted false claim is a `badAlpha` transcript. -/
theorem sound (d : Nat) : ∀ (n : Nat) (G : (Fin n → K) → K) (c : K) (polys : Fin n → K[X])
    (α : Fin n → K), IndDeg d n G → accept d n G c polys α → bsum n G ≠ c →
    badAlpha d n G polys α := by
  intro n
  induction n with
  | zero =>
      intro G c _ _ _ hacc hne
      exact absurd hacc hne
  | succ n ih =>
      intro G c polys α hdeg hacc hne
      obtain ⟨⟨h, hhd, hh⟩, hrest⟩ := hdeg
      obtain ⟨hpd, hsum, hacc'⟩ := hacc
      have hph : polys 0 ≠ h := by
        intro he
        apply hne
        rw [← hsum, he, hh 0, hh 1]
        rfl
      by_cases hroot : (polys 0 - h).eval (α 0) = 0
      · exact Or.inl ⟨h, hhd, hh, hph, hroot⟩
      · have hne' : bsum n (fun v => G (Fin.cons (α 0) v)) ≠ (polys 0).eval (α 0) := by
          intro he
          apply hroot
          rw [eval_sub, hh, he, sub_self]
        exact Or.inr (ih (fun v => G (Fin.cons (α 0) v)) ((polys 0).eval (α 0))
          (Fin.tail polys) (Fin.tail α) (hrest (α 0)) hacc' hne')

#print axioms sound
end R0P.Sumcheck
