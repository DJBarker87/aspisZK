import NearGammaMessageCover
import EarlyC1LateProjection
import AspisFormal.K1.V7ExactCorrelatedAgreement

/-! The actual original-code scalar-power gamma cover yields coefficient
messages and identifies C1 fixed before arbitrary late C2. No quotient/raw
word substitution, decoder membership or acceptance premise is used. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.NearGammaSelectedC1
open Polynomial Finset
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaFibreBridge AspisV8.NearGammaDichotomy
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
abbrev K := QM31Exact
noncomputable local instance : Fintype (Fin 262144) :=
  AspisV8.EarlyC1Specialization.explicit_instance

/-- Actual selected original-code evaluator, packed by the proved source
fibre map. Linearity is reused from pinned V7, not postulated. -/
def fibreLinear : Message →ₗ[K] (Fin 262144 → Fin 4 → K) where
  toFun := fibreEncode
  map_add' := by
    intro a b
    funext f s
    exact congrFun (AspisK1.V7ExactCorrelatedAgreement.exactInitialEncoder_add a b)
      (fibreEmbed (f,s))
  map_smul' := by
    intro scalar a
    funext f s
    exact congrFun (AspisK1.V7ExactCorrelatedAgreement.exactInitialEncoder_smul scalar a)
      (fibreEmbed (f,s))

theorem fibreLinear_apply (p : Message) : fibreLinear p=fibreEncode p := rfl

def code : Submodule K (Fin 262144 → Fin 4 → K) := LinearMap.range fibreLinear
def curve (c1 : C1Received) (c2 : C2Received) : Fin 262144 → Fin 4 → K[X] :=
  NearGammaMessageCover.curve (fibreWord29 c1 c2)
def rawBatch (c1 : C1Received) (c2 : C2Received) (gamma : K) : Fin 1048576 → K :=
  fun index => ∑ lane : Fin 29, gamma^lane.val * received29 c1 c2 lane index
def near (c1 : C1Received) (c2 : C2Received) (gamma : K)
    (u : Fin 262144 → Fin 4 → K) : Prop :=
  IsNear code univ (curve c1 c2) 9301 gamma u
def good (c1 : C1Received) (c2 : C2Received) (G : Finset K) : Finset K :=
  NearGammaDichotomy.good code univ (curve c1 c2) 9301 G

theorem domain_card : (univ : Finset (Fin 262144)).card=262144 :=
  (Finset.card_univ).trans
    ((@Fintype.card_congr (Fin 262144) (Fin 262144)
      AspisV8.EarlyC1Specialization.explicit_instance (Fin.fintype 262144)
      (Equiv.refl _)).trans (Fintype.card_fin 262144))

theorem curve_eval (c1 : C1Received) (c2 : C2Received)
    (gamma : K) (f : Fin 262144) (s : Fin 4) :
    (curve c1 c2 f s).eval gamma=rawBatch c1 c2 gamma (fibreEmbed (f,s)) :=
  NearGammaMessageCover.curve_eval (fibreWord29 c1 c2) f s gamma

theorem near_encoded_iff (c1 : C1Received) (c2 : C2Received) (gamma : K)
    (message : Message) :
    near c1 c2 gamma (fibreEncode message) ↔
      (univ.filter fun f : Fin 262144 =>
        (fun s : Fin 4 => rawBatch c1 c2 gamma (fibreEmbed (f,s))) ≠
          fibreEncode message f).card ≤ 9301 := by
  change (_ ∧ _) ↔ _
  have member : fibreEncode message ∈ code := ⟨message,rfl⟩
  simp_rw [curve_eval]
  exact and_iff_right member

/-- Original-code tuples are constructed before gamma, and their C1
projection equals the unchanged optional object determined only by C1.
The sparse alternative is retained even if no near candidate exists. -/
theorem selected_gamma_c1_dichotomy (c1 : C1Received) (c2 : C2Received)
    (G : Finset K) :
    (good c1 c2 G).card<64 ∨
      ∃ p : Fin 29 → Message,
        245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card ∧
        earlyC1 c1=some (c1Projection p) ∧
        ∀ gamma ∈ G, ∀ u, near c1 c2 gamma u →
          u=fibreEncode (NearGammaMessageCover.batch p gamma) := by
  have split := NearGammaMessageCover.message_cover_dichotomy fibreLinear
    (fibreWord29 c1 c2) G domain_card AspisV8.EarlyC1Identification.matching_set_cap
  rcases split with sparse | ⟨p,own,covered⟩
  · exact Or.inl sparse
  · exact Or.inr ⟨p,own,late_projection_identifies c1 c2 p own,covered⟩

/-- Absence of the early optional C1 candidate rules out the dense branch,
not by dropping provider-none executions but by the derived own support. -/
theorem no_early_c1_forces_sparse (c1 : C1Received) (c2 : C2Received)
    (G : Finset K) (absent : earlyC1 c1=none) : (good c1 c2 G).card<64 := by
  rcases selected_gamma_c1_dichotomy c1 c2 G with sparse | ⟨p,own,found,covered⟩
  · exact sparse
  · have impossible := found.symm.trans absent
    cases impossible

#print axioms fibreLinear
#print axioms domain_card
#print axioms curve_eval
#print axioms near_encoded_iff
#print axioms selected_gamma_c1_dichotomy
#print axioms no_early_c1_forces_sparse
end
end AspisV8.NearGammaSelectedC1
