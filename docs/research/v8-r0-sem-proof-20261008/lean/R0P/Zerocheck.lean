import R0P.Sumcheck
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Lead: zerocheck batching on top of `Sumcheck.sound`.

The pair-forest sumcheck target (pair_forest_semantic_terminal.rs:1303–1308)
at a Boolean row b is `eq(zc,b)·comp(b) + μ·H1(b) + μ²·inact(b)` with
`comp(b) = Σ_i θ^i lane_i(b)` over the 29 θ-lanes. Its hypercube sum is
`mle(comp)(zc) + μ·ΣH1 + μ²·Σinact`. Outside the α, μ, zc and θ bad sets
(ledger branches sumcheckRounds, muBatch, zerocheckPoint, thetaLane), an
accepted claim of 0 forces every lane to vanish on every row and both helper
sums to vanish. The bad sets are definitions here; their cardinalities are
the G10 obligations. -/
set_option autoImplicit false
namespace R0P.Sumcheck
open Polynomial

variable {K : Type} [Field K]

def ofBool {n : Nat} (b : Fin n → Bool) : Fin n → K := fun i => if b i then 1 else 0

theorem ofBool_cons (n : Nat) (x : Bool) (b : Fin n → Bool) :
    (ofBool (Fin.cons x b) : Fin (n+1) → K) = Fin.cons (if x then 1 else 0) (ofBool b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [ofBool, Fin.cons_zero]
  · simp only [ofBool, Fin.cons_succ]

/-- `Σ_{b ∈ {0,1}^n} f b`, by recursion. -/
def bsumB : (n : Nat) → ((Fin n → Bool) → K) → K
  | 0, f => f (fun i => i.elim0)
  | n+1, f => bsumB n (fun b => f (Fin.cons false b)) + bsumB n (fun b => f (Fin.cons true b))

theorem bsum_eq_bsumB : ∀ (n : Nat) (G : (Fin n → K) → K),
    bsum n G = bsumB n (fun b => G (ofBool b))
  | 0, G => by
      simp only [bsum, bsumB]
      congr 1
      funext i
      exact i.elim0
  | n+1, G => by
      simp only [bsum, bsumB]
      rw [bsum_eq_bsumB n, bsum_eq_bsumB n]
      congr 1 <;> congr 1 <;> funext b <;> rw [ofBool_cons] <;> rfl

/-- `eq(z, b)` at a Boolean point. -/
def eqwB : (n : Nat) → (Fin n → K) → (Fin n → Bool) → K
  | 0, _, _ => 1
  | n+1, z, b => (if b 0 then z 0 else 1 - z 0) * eqwB n (Fin.tail z) (Fin.tail b)

/-- The multilinear extension, evaluated at `z`. -/
def mle : (n : Nat) → ((Fin n → Bool) → K) → (Fin n → K) → K
  | 0, f, _ => f (fun i => i.elim0)
  | n+1, f, z => (1 - z 0) * mle n (fun b => f (Fin.cons false b)) (Fin.tail z) +
      z 0 * mle n (fun b => f (Fin.cons true b)) (Fin.tail z)

theorem bsumB_smul : ∀ (n : Nat) (k : K) (f : (Fin n → Bool) → K),
    bsumB n (fun b => k * f b) = k * bsumB n f
  | 0, _, _ => rfl
  | n+1, k, f => by
      simp only [bsumB]
      rw [bsumB_smul n, bsumB_smul n, mul_add]

theorem bsumB_add : ∀ (n : Nat) (f g : (Fin n → Bool) → K),
    bsumB n (fun b => f b + g b) = bsumB n f + bsumB n g
  | 0, _, _ => rfl
  | n+1, f, g => by
      simp only [bsumB]
      rw [bsumB_add n, bsumB_add n]
      ring

theorem bsumB_eqw : ∀ (n : Nat) (z : Fin n → K) (f : (Fin n → Bool) → K),
    bsumB n (fun b => eqwB n z b * f b) = mle n f z
  | 0, _, _ => by simp only [bsumB, eqwB, mle, one_mul]
  | n+1, z, f => by
      simp only [bsumB, eqwB, mle, Fin.cons_zero, Fin.tail_cons, Bool.false_eq_true,
        ↓reduceIte]
      rw [← bsumB_eqw n, ← bsumB_eqw n, ← bsumB_smul, ← bsumB_smul]
      congr 1 <;> congr 1 <;> funext b <;> ring

/-- `Σ_i θ^i lane_i(b)`, the θ-batched row composition. -/
def lanesComp (θ : K) (lanes : Fin 29 → (Fin 10 → Bool) → K) (b : Fin 10 → Bool) : K :=
  ∑ i : Fin 29, θ ^ i.val * lanes i b

/-- Ledger branch sumcheckRounds: `Sumcheck.sound`'s witness event. -/
def BadAlpha (d n : Nat) (α : Fin n → K) : Prop :=
  ∃ i : Fin n, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ p.eval (α i) = 0

/-- Ledger branch muBatch: μ is a root of a nonzero degree-≤2 polynomial. -/
def BadMu (a s1 s2 μ : K) : Prop :=
  (a ≠ 0 ∨ s1 ≠ 0 ∨ s2 ≠ 0) ∧ a + μ * s1 + μ ^ 2 * s2 = 0

/-- Ledger branch zerocheckPoint: zc is a zero of a nonzero multilinear extension. -/
def BadZc (f : (Fin 10 → Bool) → K) (z : Fin 10 → K) : Prop :=
  (∃ b, f b ≠ 0) ∧ mle 10 f z = 0

/-- Ledger branch thetaLane: some lane is nonzero yet the θ-batched row
function vanishes identically; at a witnessing row θ is a root of a nonzero
degree-≤28 polynomial. -/
def BadTheta (lanes : Fin 29 → (Fin 10 → Bool) → K) (θ : K) : Prop :=
  (∃ i b, lanes i b ≠ 0) ∧ ∀ b, lanesComp θ lanes b = 0

theorem compose (lanes : Fin 29 → (Fin 10 → Bool) → K) (H1 inact : (Fin 10 → Bool) → K)
    (θ μ : K) (zc : Fin 10 → K) (G : (Fin 10 → K) → K) (polys : Fin 10 → K[X]) (α : Fin 10 → K)
    (hG : ∀ b, G (ofBool b) = eqwB 10 zc b * lanesComp θ lanes b + μ * H1 b + μ ^ 2 * inact b)
    (hdeg : IndDeg 27 10 G) (hacc : accept 27 10 G 0 polys α)
    (hα : ¬ BadAlpha 27 10 α)
    (hμ : ¬ BadMu (mle 10 (lanesComp θ lanes) zc) (bsumB 10 H1) (bsumB 10 inact) μ)
    (hzc : ¬ BadZc (lanesComp θ lanes) zc) (hθ : ¬ BadTheta lanes θ) :
    (∀ i b, lanes i b = 0) ∧ bsumB 10 H1 = 0 ∧ bsumB 10 inact = 0 := by
  have hsum : bsum 10 G = 0 := by
    by_contra hne
    exact hα (sound 27 10 G 0 polys α hdeg hacc hne)
  rw [bsum_eq_bsumB] at hsum
  have he : (fun b => G (ofBool b)) =
      fun b => (eqwB 10 zc b * lanesComp θ lanes b + μ * H1 b) + μ ^ 2 * inact b := by
    funext b
    rw [hG]
  rw [he, bsumB_add, bsumB_add, bsumB_eqw, bsumB_smul, bsumB_smul] at hsum
  have h3 : mle 10 (lanesComp θ lanes) zc = 0 ∧ bsumB 10 H1 = 0 ∧ bsumB 10 inact = 0 := by
    by_contra hc
    apply hμ
    refine ⟨?_, hsum⟩
    tauto
  obtain ⟨hm, h1, h2⟩ := h3
  refine ⟨?_, h1, h2⟩
  have hcomp : ∀ b, lanesComp θ lanes b = 0 := by
    by_contra hc
    push Not at hc
    exact hzc ⟨hc, hm⟩
  by_contra hc
  push Not at hc
  exact hθ ⟨hc, hcomp⟩

#print axioms bsum_eq_bsumB
#print axioms bsumB_eqw
#print axioms compose
end R0P.Sumcheck
