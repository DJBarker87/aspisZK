import R1Z.CertLiftEntry
import R1Z.CertNatural
import R1Z.CertBuildIdent
import R1Z.RfObs

/-! D59.2 builder 2: the extracted lift columns are the Lean lift coordinates.

Part A: the builder's `K` values equal the `RfOwn` closed forms (`rustEq`,
`rustPoints`, `rustHWeight`, `rustEvalRow`), with `natR = naturalLineValue`
(`CertNatural`).  Part B: each C1/H1 lift entry is `φ` of the corresponding
`flatC1`/`flatH1` coordinate of `obs (c1Src r)` / `obs (h1Src r k)`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R0P.SemSource R1Z.RfChain R1Z.RfOwn R1Z.RfObs R1Z.RfSrc
open R0Z.K4 R0Z.HonestView AspisCircleTensorBinding
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

/-! ### Part A: closed forms -/

theorem sc_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩) :
    ∀ n, n ≤ 10 → scK A n = succCarry α n
  | 0, _ => by simp [scK, succCarry]
  | n + 1, hn => by
      rw [scK, Finset.prod_range_succ, ← scK, sc_eq α A hA n (by omega), succCarry, dif_pos (by omega),
        hA _ (by omega), mul_comm]

theorem pc_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (g c : ℕ) (hg : g < 3) (hc : c < 10) : pcK A g c = rustPoints α ⟨g, hg⟩ ⟨c, hc⟩ := by
  unfold pcK
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
  · simp [rustPoints, hA c hc]
  · simp only [rustPoints, successorPoint, if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true]
    rw [sc_eq α A hA _ (by omega), hA c hc]
  · simp only [rustPoints, xor12Point, if_neg (show (2 : ℕ) ≠ 0 by norm_num),
      if_neg (show (2 : ℕ) ≠ 1 by norm_num), hA c hc]

theorem eq_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (g : ℕ) (hg : g < 3) (r : Fin 1024) : eqK A g r.val = rustEq (rustPoints α ⟨g, hg⟩) r := by
  unfold eqK rustEq
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pc_eq α A hA g i hg i.2]
  rcases Nat.mod_two_eq_zero_or_one (r.val / 2 ^ (9 - i.val)) with h | h
  · rw [h, if_neg (by omega)]; simp
  · rw [h, if_pos rfl]; push_cast; ring

theorem hw_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (co : Fin 1024) : hwK A co.val = rustHWeight α co := by
  unfold hwK rustHWeight
  rw [hA 8 (by norm_num), hA 9 (by norm_num)]
  rfl

theorem ev_eq (X Y : K) (co : Fin 1024) : evK X Y co.val = rustEvalRow co X Y := by
  unfold evK rustEvalRow
  rw [natR_eq X 10 (co.val / 2) (by have := co.2; norm_num; omega)]

/-- The Rust head value of cell `g` of row `r` (claims, extra, OOD). -/
def cellK (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (r : Fin 1024) (g : ℕ) : K :=
  if h : g < 3 then rustEq (rustPoints (alpha ch) ⟨g, h⟩) r
  else if g = 3 then rustHWeight (alpha ch) (π r)
  else if g = 4 then rustEvalRow (π r) (ch.circle 0).1.1 (ch.circle 0).1.2
  else rustEvalRow (π r) (ch.circle 1).1.1 (ch.circle 1).1.2

theorem head_eq (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (al zz tr : Slice U32)
    (ha : ∀ (j : ℕ) (h : j < 10), Alimb B φ al j = alpha ch ⟨j, h⟩)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (ch.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (ch.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val) (r : Fin 1024) (g : ℕ) (hg : g < 6) :
    headK (Alimb B φ al) (Alimb B φ zz) (gN tr r.val) r.val g = cellK π ch r g := by
  unfold headK cellK
  by_cases g3 : g < 3
  · rw [if_pos g3, dif_pos g3, eq_eq (alpha ch) _ ha g g3 r]
  · rw [if_neg g3, dif_neg g3]
    by_cases g4 : g = 3
    · rw [if_pos g4, if_pos g4, htr, hw_eq (alpha ch) _ ha]
    · rw [if_neg g4, if_neg g4, htr]
      by_cases g5 : g = 4
      · subst g5
        rw [if_pos rfl, ← ev_eq, show 2 * (4 - 4) = 2 * (0 : Fin 2).val by rfl, hzx 0, hzy 0]
      · have g5' : g = 5 := by omega
        subst g5'
        rw [if_neg (by norm_num), ← ev_eq, show 2 * (5 - 4) = 2 * (1 : Fin 2).val by rfl, hzx 1, hzy 1]

#print axioms eq_eq
#print axioms hw_eq
#print axioms ev_eq
#print axioms head_eq

end R1Z.CertBuild
