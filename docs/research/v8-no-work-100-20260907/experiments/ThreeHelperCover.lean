import NearGammaDichotomy

/-! Three nodal codewords construct a pre-challenge cover of a quadratic
received curve. D is an arbitrary fixed support: excluded C1 fibres never
enter the agreement predicate or the overlap count. This is existence and
coverage, not an efficient decoder or an acceptance probability theorem. -/
set_option autoImplicit false
namespace AspisV8.ThreeHelperCover
open Polynomial Finset
open AspisV8.NearGammaCover AspisV8.NearGammaDichotomy
variable {K Pos Slot : Type*} [Field K] [DecidableEq K] [DecidableEq Pos]
  [Fintype Slot] [DecidableEq Slot] [DecidableEq (Slot → K)]

theorem common_complement_bound (I : Finset K) (D : Finset Pos)
    (bad : K → Finset Pos) (B : ℕ)
    (cap : ∀ g∈I, (bad g).card≤B) :
    D.card≤(D\I.biUnion bad).card+I.card*B := by
  have unionCap : (I.biUnion bad).card≤I.card*B := by
    calc
      (I.biUnion bad).card≤∑ g∈I, (bad g).card := card_biUnion_le
      _≤∑ _g∈I, B := sum_le_sum cap
      _=I.card*B := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
  have partition := card_sdiff_add_card_inter D (I.biUnion bad)
  have subset := card_le_card (inter_subset_right : D∩I.biUnion bad⊆I.biUnion bad)
  omega

/-- The tuple is constructed from a fixed quadratic received curve and the
set of all near-codeword parameters. It is not supplied by a provider. -/
theorem dense_cover
    (C : Submodule K (Pos → Slot → K))
    (D : Finset Pos) (G : Finset K) (v : Pos → Slot → K[X])
    (B delta : ℕ)
    (degree : ∀ x y, (v x y).degree<3)
    (margin : 4*B+delta<D.card)
    (overlap : ∀ u∈C, ∀ w∈C, u≠w →
      (D.filter fun x => u x=w x).card≤delta)
    (dense : 3≤(good C D v B G).card) :
    ∃ p : Fin 3 → Pos → Slot → K,
      (∀ lane, p lane∈C) ∧
      ∀ g∈G, ∀ u, IsNear C D v B g u →
        u=fun x y => ∑ lane : Fin 3, g^lane.val*p lane x y := by
  classical
  obtain ⟨I,sub,cardI⟩ := exists_subset_card_eq dense
  have goodNear : ∀ g∈I, ∃ u, IsNear C D v B g u := by
    intro g hg
    exact (by simpa [good] using sub hg :
      g∈G ∧ ∃ u, IsNear C D v B g u).2
  let cand : K → Pos → Slot → K := fun g =>
    if hg : g∈I then Classical.choose (goodNear g hg) else 0
  have candNear : ∀ g∈I, IsNear C D v B g (cand g) := by
    intro g hg
    dsimp [cand]
    rw [dif_pos hg]
    exact Classical.choose_spec (goodNear g hg)
  let bad : K → Finset Pos := fun g =>
    D.filter fun x => (fun y => (v x y).eval g)≠cand g x
  let common := D\I.biUnion bad
  have commonSubset : common⊆D := sdiff_subset
  have commonLarge : B+delta<common.card := by
    have lower := common_complement_bound I D bad B
      (fun g hg => (candNear g hg).2)
    rw [cardI] at lower
    change D.card≤common.card+3*B at lower
    omega
  have candCode : ∀ g∈I, cand g∈C := fun g hg => (candNear g hg).1
  have hmatch : ∀ g∈I, ∀ x∈common, ∀ y, (v x y).eval g=cand g x y := by
    intro g hg x hx y
    have outside := (mem_sdiff.mp hx).2
    have equal : (fun y => (v x y).eval g)=cand g x := by
      by_contra unequal
      apply outside
      apply mem_biUnion.mpr
      refine ⟨g,hg,?_⟩
      exact mem_filter.mpr ⟨commonSubset hx,unequal⟩
    exact congrFun equal y
  have degreeI : ∀ x y, (v x y).degree<I.card := by
    simpa [cardI] using degree
  have covered : ∀ g u, IsNear C D v B g u →
      u=fun x y => (interp I cand x y).eval g := by
    intro g u near
    exact covers_all_near C D common I v cand B delta candCode
      commonSubset degreeI hmatch commonLarge overlap g u near.1 near.2
  let p : Fin 3 → Pos → Slot → K := fun lane x y =>
    (interp I cand x y).coeff lane.val
  refine ⟨p,?_,?_⟩
  · intro lane
    exact interp_code_coeff C I cand candCode lane.val
  · intro g hg u near
    rw [covered g u near]
    funext x y
    have degreeP : (interp I cand x y).natDegree<3 := by
      by_cases zero : interp I cand x y=0
      · simp only [zero,natDegree_zero]; omega
      · apply (natDegree_lt_iff_degree_lt zero).mpr
        simpa only [interp,Lagrange.interpolate_apply,cardI] using
          Lagrange.degree_interpolate_lt
            (r:=fun g => cand g x y) (s:=I) (v:=id)
            (fun _ _ _ _ h => h)
    rw [Polynomial.eval_eq_sum_range' degreeP,← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro lane _
    exact mul_comm _ _

/-- Sparse good gamma values remain an explicit alternative. The dense
branch covers every near candidate, including post-gamma selections. -/
theorem cover_dichotomy
    (C : Submodule K (Pos → Slot → K))
    (D : Finset Pos) (G : Finset K) (v : Pos → Slot → K[X])
    (B delta : ℕ)
    (degree : ∀ x y, (v x y).degree<3)
    (margin : 4*B+delta<D.card)
    (overlap : ∀ u∈C, ∀ w∈C, u≠w →
      (D.filter fun x => u x=w x).card≤delta) :
    (good C D v B G).card<3 ∨
      ∃ p : Fin 3 → Pos → Slot → K,
        (∀ lane, p lane∈C) ∧
        ∀ g∈G, ∀ u, IsNear C D v B g u →
          u=fun x y => ∑ lane : Fin 3, g^lane.val*p lane x y := by
  by_cases sparse : (good C D v B G).card<3
  · exact Or.inl sparse
  · exact Or.inr (dense_cover C D G v B delta degree margin overlap (by omega))

#print axioms common_complement_bound
#print axioms dense_cover
#print axioms cover_dichotomy
end AspisV8.ThreeHelperCover
