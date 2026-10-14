import R1InitialResponses

/-! Padding and projection facts for a partially specified width-29 family.
These are finite-set consequences of the existing full joint list bound; they
do not define an efficient decoder or an extraction algorithm. -/
set_option autoImplicit false
namespace AspisR1.PartialJointList
noncomputable section

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisR1.InitialResponses AspisR1.JointList
open AspisV6Width29CorrelatedAgreement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def projectWord (S : Finset (Fin 29)) (W : Fin 29 → InitialWord K) :
    Fin 29 → InitialWord K :=
  fun lane => if lane ∈ S then W lane else 0

def projectMessage (S : Finset (Fin 29)) (t : Fin 29 → InitialMessage K) :
    Fin 29 → InitialMessage K :=
  fun lane => if lane ∈ S then t lane else 0

def selectedSupport (S : Finset (Fin 29)) (W : Fin 29 → InitialWord K)
    (t : Fin 29 → InitialMessage K) : Finset (Fin 1048576) := by
  classical
  exact Finset.univ.filter fun x => ∀ lane, lane ∈ S → W lane x = exactInitialEncoder (t lane) x

theorem exactInitialEncoder_zero : exactInitialEncoder (0 : InitialMessage K) =
    (0 : InitialWord K) := by
  simpa only [exactInitialLinear_apply] using exactInitialLinear.map_zero

theorem selectedSupport_eq_joint (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K) :
    selectedSupport S W t =
      width29JointAgreementSet exactInitialEncoder (projectWord S W)
        (projectMessage S t) := by
  classical
  ext x
  simp only [selectedSupport, width29JointAgreementSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h lane
    by_cases hlane : lane ∈ S
    · simpa [projectWord, projectMessage, hlane] using h lane hlane
    · simp [projectWord, projectMessage, hlane, exactInitialEncoder_zero]
  · intro h lane hlane
    simpa [projectWord, projectMessage, hlane] using h lane

theorem projectMessage_mem_Lambda (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K)
    (ht : t ∈ InitialResponses.Lambda W) :
    projectMessage S t ∈ InitialResponses.Lambda (projectWord S W) := by
  rw [InitialResponses.mem_Lambda] at ht ⊢
  have hsubset : width29JointAgreementSet exactInitialEncoder W t ⊆
      width29JointAgreementSet exactInitialEncoder (projectWord S W)
        (projectMessage S t) := by
    intro x hx
    simp only [width29JointAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    intro lane
    by_cases hlane : lane ∈ S
    · simpa [projectWord, projectMessage, hlane] using hx lane
    · simp [projectWord, projectMessage, hlane, exactInitialEncoder_zero]
  have hcard := Finset.card_le_card hsubset
  omega

def partialJointAgreementSet (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K) :
    Finset (Fin 1048576) := selectedSupport S W t

/-- A family supported on the selected coordinates inherits the same 100-list
bound from the full width-29 joint agreement theorem after zero padding. -/
theorem partial_family_card_le_100 (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (supported : ∀ t ∈ family, ∀ lane, lane ∉ S → t lane = 0)
    (close : ∀ t ∈ family,
      38230 ≤ (partialJointAgreementSet S W t).card) :
    family.card ≤ 100 := by
  classical
  let projected := family.image (projectMessage S)
  have fixed : ∀ t ∈ family, projectMessage S t = t := by
    intro t ht
    funext lane
    by_cases hlane : lane ∈ S
    · simp [projectMessage, hlane]
    · simp [projectMessage, hlane, supported t ht lane hlane]
  have family_subset : family ⊆ projected := by
    intro t ht
    apply Finset.mem_image.mpr
    exact ⟨t, ht, fixed t ht⟩
  have projected_close : ∀ t ∈ projected,
      38230 ≤ (width29JointAgreementSet exactInitialEncoder
        (projectWord S W) t).card := by
    intro t ht
    obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp ht
    rw [← selectedSupport_eq_joint]
    exact close original horiginal
  have projected_bound := jointInitialList_card_le_100
    (projectWord S W) projected projected_close
  exact (Finset.card_le_card family_subset).trans projected_bound

#print axioms exactInitialEncoder_zero
#print axioms selectedSupport_eq_joint
#print axioms projectMessage_mem_Lambda
#print axioms partial_family_card_le_100

end AspisR1.PartialJointList
end
