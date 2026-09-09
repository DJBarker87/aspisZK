import NearGammaDichotomy
import EarlyC1Support

/-! Extract message coefficients from the constructed code-valued gamma
curve. The received lanes are arbitrary. No provider, decoder or candidate
membership is assumed. This remains a noncomputable mathematical cover. -/
set_option autoImplicit false
namespace AspisV8.NearGammaMessageCover
open Polynomial Finset
open AspisV8.NearGammaDichotomy AspisV8.EarlyC1Projection
open AspisV5FriConcreteEncoderApplicability
variable {K Pos Slot M : Type*} [Field K] [DecidableEq K]
  [Fintype Pos] [DecidableEq Pos] [Fintype Slot] [DecidableEq Slot]
  [AddCommGroup M] [Module K M]
noncomputable section

def curve (received : Fin 29 → Pos → Slot → K) : Pos → Slot → K[X] :=
  fun x y => monomialPolynomial (fun lane => received lane x y)

theorem curve_coeff (received : Fin 29 → Pos → Slot → K)
    (x : Pos) (y : Slot) (lane : Fin 29) :
    (curve received x y).coeff lane.val = received lane x y :=
  monomialPolynomial_coeff _ lane

theorem curve_eval (received : Fin 29 → Pos → Slot → K)
    (x : Pos) (y : Slot) (gamma : K) :
    (curve received x y).eval gamma =
      ∑ lane : Fin 29, gamma ^ lane.val * received lane x y := by
  simp only [curve, monomialPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem curve_degree (received : Fin 29 → Pos → Slot → K) (x : Pos) (y : Slot) :
    (curve received x y).degree < 29 := by
  have h := monomialPolynomial_natDegree_le (show 0<29 by omega)
    (fun lane => received lane x y)
  change (curve received x y).natDegree ≤ 28 at h
  exact (degree_le_natDegree).trans_lt (by exact_mod_cast (show (curve received x y).natDegree<29 by omega))

def batch (p : Fin 29 → M) (gamma : K) : M :=
  ∑ lane : Fin 29, gamma ^ lane.val • p lane

theorem encode_batch (E : M →ₗ[K] (Pos → Slot → K))
    (p : Fin 29 → M) (gamma : K) :
    E (batch p gamma) = fun x y => ∑ lane : Fin 29, gamma ^ lane.val * E (p lane) x y := by
  rw [batch, map_sum]
  simp_rw [map_smul]
  funext x y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The overlap interface speaks about code messages on arbitrary witnessed
sets, avoiding a concrete independently-created filter identity. -/
theorem range_overlap (E : M →ₗ[K] (Pos → Slot → K))
    (cap : ∀ left right : M, left ≠ right → ∀ s : Finset Pos,
      (∀ x ∈ s, E left x = E right x) → s.card ≤ 256) :
    ∀ u ∈ LinearMap.range E, ∀ w ∈ LinearMap.range E, u ≠ w →
      (univ.filter fun x => u x = w x).card ≤ 256 := by
  classical
  intro u hu w hw different
  obtain ⟨left,rfl⟩ := hu
  obtain ⟨right,rfl⟩ := hw
  apply cap left right (fun eq => different (congrArg E eq))
  intro x hx
  exact (mem_filter.mp hx).2

/-- A pre-gamma coefficient tuple is constructed in the dense branch.
Its own support, rather than a sampled batch's complete matching support,
is what subsequently identifies the earlier optional C1 object. -/
theorem message_cover_dichotomy (E : M →ₗ[K] (Pos → Slot → K))
    (received : Fin 29 → Pos → Slot → K) (G : Finset K)
    (domain : (univ : Finset Pos).card=262144)
    (cap : ∀ left right : M, left ≠ right → ∀ s : Finset Pos,
      (∀ x ∈ s, E left x = E right x) → s.card ≤ 256) :
    (good (LinearMap.range E) univ (curve received) 9301 G).card<64 ∨
      ∃ p : Fin 29 → M,
        245609 ≤ (support E received p).card ∧
        ∀ gamma ∈ G, ∀ u, IsNear (LinearMap.range E) univ
          (curve received) 9301 gamma u → u=E (batch p gamma) := by
  classical
  rcases constructed_cover_dichotomy (LinearMap.range E) univ G (curve received)
      domain (curve_degree received) (range_overlap E cap) with sparse | ⟨words,inCode,own,covered⟩
  · exact Or.inl sparse
  · choose p encoded using inCode
    right
    refine ⟨p, ?_, ?_⟩
    · apply own.trans (card_le_card ?_)
      intro x hx
      letI : DecidablePred (fun z => ∀ lane : Fin 29, received lane z = E (p lane) z) :=
        fun _ => Classical.propDecidable _
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro lane
      funext y
      have he := (mem_filter.mp hx).2 y lane
      rw [curve_coeff] at he
      exact he.trans (congrFun (congrFun (encoded lane).symm x) y)
    · intro gamma hg u hu
      rw [encode_batch]
      have he := covered gamma hg u hu
      rw [he]
      funext x y
      apply Finset.sum_congr rfl
      intro lane _
      rw [encoded lane]

#print axioms curve_coeff
#print axioms curve_eval
#print axioms curve_degree
#print axioms encode_batch
#print axioms range_overlap
#print axioms message_cover_dichotomy
end
end AspisV8.NearGammaMessageCover
