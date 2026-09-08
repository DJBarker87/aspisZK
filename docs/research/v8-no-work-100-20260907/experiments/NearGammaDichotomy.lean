import NearGammaSupport
import NearGammaCover
import NearGammaOwnSupport
import NearGammaArithmetic

/-! The target curve is constructed before the actual gamma. `good` is
defined only from the fixed received curve and code. No decoder provider or
post-gamma candidate is an input to the conclusion. -/
set_option autoImplicit false
namespace AspisV8.NearGammaDichotomy
open Polynomial Finset
open AspisV8.NearGammaSupport AspisV8.NearGammaCover
open AspisV8.NearGammaOwnSupport

variable {K Pos Slot : Type*} [Field K] [DecidableEq K] [DecidableEq Pos]
  [Fintype Slot] [DecidableEq Slot] [DecidableEq (Slot → K)]
abbrev Word := Pos → Slot → K

def IsNear (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (v : Pos → Slot → K[X]) (B : ℕ) (g : K)
    (u : Word (K:=K) (Pos:=Pos) (Slot:=Slot)) : Prop :=
  u ∈ C ∧ (D.filter fun x => (fun y => (v x y).eval g) ≠ u x).card ≤ B

noncomputable def good
    (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (v : Pos → Slot → K[X]) (B : ℕ) (G : Finset K) : Finset K :=
  by
    classical
    exact G.filter fun g => ∃ u, IsNear C D v B g u

theorem dense_constructed_cover
    (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (G : Finset K) (v : Pos → Slot → K[X])
    (hD : D.card = 262144)
    (degree : ∀ x y, (v x y).degree < 29)
    (overlap : ∀ u ∈ C, ∀ w ∈ C, u ≠ w →
      (D.filter fun x => u x = w x).card ≤ 256)
    (certificate : 9557 * Nat.choose 64 29 < 113328 * Nat.choose 61 29)
    (hgood : 64 ≤ (good C D v 9301 G).card) :
    ∃ p : Fin 29 → Word (K:=K) (Pos:=Pos) (Slot:=Slot),
      (∀ lane, p lane ∈ C) ∧
      245609 ≤ (D.filter fun x => ∀ y lane, (v x y).coeff lane.val = p lane x y).card ∧
      ∀ g ∈ G, ∀ u, IsNear C D v 9301 g u →
        u = fun x y => ∑ lane : Fin 29, g ^ lane.val * p lane x y := by
  classical
  obtain ⟨S,hSG,hS⟩ := exists_subset_card_eq hgood
  have goodNear : ∀ g ∈ S, ∃ u, IsNear C D v 9301 g u := by
    intro g hg
    exact (by simpa [good] using hSG hg :
      g ∈ G ∧ ∃ u, IsNear C D v 9301 g u).2
  let cand : K → Word (K:=K) (Pos:=Pos) (Slot:=Slot) := fun g =>
    if hg : g ∈ S then Classical.choose (goodNear g hg) else 0
  have candNear : ∀ g ∈ S, IsNear C D v 9301 g (cand g) := by
    intro g hg
    dsimp [cand]
    rw [dif_pos hg]
    exact Classical.choose_spec (goodNear g hg)
  let A : K → Finset Pos := fun g =>
    D.filter fun x => (fun y => (v x y).eval g) = cand g x
  have nearA : ∀ g ∈ S, (D \ A g).card ≤ 9301 := by
    intro g hg
    have hn := (candNear g hg).2
    have he : D \ A g =
        D.filter fun x => (fun y => (v x y).eval g) ≠ cand g x := by
      ext x
      simp only [mem_sdiff, mem_filter, A]
      tauto
    rw [he]
    exact hn
  obtain ⟨I,hIpow,hlarge⟩ :=
    common_64_29 S D A hS hD nearA certificate
  have hIS : I ⊆ S := (mem_powersetCard.mp hIpow).1
  have hIcard : I.card = 29 := (mem_powersetCard.mp hIpow).2
  let common := D.filter fun x => ∀ g ∈ I, x ∈ A g
  have commonLarge : 9301+256 < common.card := by
    dsimp [common]
    omega
  have candCode : ∀ g ∈ I, cand g ∈ C := by
    intro g hg
    exact (candNear g (hIS hg)).1
  have hmatch : ∀ g ∈ I, ∀ x ∈ common, ∀ y,
      (v x y).eval g = cand g x y := by
    intro g hg x hx y
    have ha := (mem_filter.mp hx).2 g hg
    exact congrFun (mem_filter.mp ha).2 y
  let p : Fin 29 → Word (K:=K) (Pos:=Pos) (Slot:=Slot) := fun lane x y =>
    (interp I cand x y).coeff lane.val
  have allCovered (g : K) (u : Word (K:=K) (Pos:=Pos) (Slot:=Slot))
      (hu : IsNear C D v 9301 g u) :
      u = fun x y => (interp I cand x y).eval g := by
    have degreeI : ∀ x y, (v x y).degree < I.card := by
      simpa [hIcard] using degree
    exact covers_all_near C D common I v cand 9301 256
      candCode (filter_subset _ _) degreeI hmatch commonLarge overlap g u hu.1 hu.2
  have own := own_support_64_29 D S I v cand hD hS hIcard degree
    (fun g hg => (candNear g hg).2)
    (fun g hg => allCovered g (cand g) (candNear g hg))
  refine ⟨p, ?_, ?_, ?_⟩
  · intro lane
    exact interp_code_coeff C I cand candCode lane.val
  · apply own.trans (card_le_card ?_)
    intro x hx
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hx).1, ?_⟩
    intro y lane
    exact congrArg (fun f : K[X] => f.coeff lane.val) ((mem_filter.mp hx).2 y)
  · intro g hg u hu
    have covered := allCovered g u hu
    rw [covered]
    funext x y
    have hdeg : (interp I cand x y).natDegree < 29 := by
      by_cases hz : interp I cand x y = 0
      · simp [hz]
      · apply (natDegree_lt_iff_degree_lt hz).mpr
        simpa [interp, Lagrange.interpolate_apply, hIcard] using Lagrange.degree_interpolate_lt
          (r := fun g => cand g x y) (s := I) (v := id)
          (fun _ _ _ _ h => h)
    rw [Polynomial.eval_eq_sum_range' hdeg]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro lane _
    simp only [p]
    ring

/-- The small branch is charged before conditioning on the actual gamma; the
large branch constructs one tuple covering all later near candidates. -/
theorem constructed_cover_dichotomy
    (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (G : Finset K) (v : Pos → Slot → K[X])
    (hD : D.card = 262144)
    (degree : ∀ x y, (v x y).degree < 29)
    (overlap : ∀ u ∈ C, ∀ w ∈ C, u ≠ w →
      (D.filter fun x => u x = w x).card ≤ 256) :
    (good C D v 9301 G).card < 64 ∨
      ∃ p : Fin 29 → Word (K:=K) (Pos:=Pos) (Slot:=Slot),
        (∀ lane, p lane ∈ C) ∧
        245609 ≤ (D.filter fun x => ∀ y lane, (v x y).coeff lane.val = p lane x y).card ∧
        ∀ g ∈ G, ∀ u, IsNear C D v 9301 g u →
          u = fun x y => ∑ lane : Fin 29, g ^ lane.val * p lane x y := by
  by_cases h : (good C D v 9301 G).card < 64
  · exact Or.inl h
  · exact Or.inr (dense_constructed_cover C D G v hD degree overlap
      AspisV8.NearGammaArithmetic.support_certificate
      (Nat.le_of_not_gt h))

#print axioms dense_constructed_cover
#print axioms constructed_cover_dichotomy
end AspisV8.NearGammaDichotomy
