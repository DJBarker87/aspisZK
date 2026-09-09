import ThreeHelperCover
import FixedC1HelperReduction
import NearGammaSelectedCoefficients

/-! Concrete original-code helper coverage on a fixed C1 own support.
The helper messages are constructed before gamma. No agreement is imposed
on excluded C1 fibres and no acceptance/efficient-extraction claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 50000
namespace AspisV8.ThreeHelperSelected
open Polynomial Finset
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaSelectedC1 AspisV8.NearGammaFibreBridge
open AspisV8.FixedC1HelperReduction AspisV8.NearGammaSelectedCoefficients
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance

def helperFibres (c2 : C2Received) : Fin 262144 → Fin 4 → K[X] :=
  fun f s => helperPolynomial c2 (fibreEmbed (f,s))
def helperBatch (h : Fin 3 → Message) (gamma : K) : Message :=
  ∑ lane : Fin 3, gamma^lane.val • h lane
def goodOn (c2 : C2Received) (S : Finset (Fin 262144)) (B : ℕ) (G : Finset K) :=
  AspisV8.NearGammaDichotomy.good code S (helperFibres c2) B G
def rawBad (received : C1Received) (c2 : C2Received) (gamma : K)
    (message : Message) (S : Finset (Fin 262144)) :=
  S.filter fun f =>
    (fun s : Fin 4 => rawBatch received c2 gamma (fibreEmbed (f,s)))≠fibreEncode message f

theorem helper_degree (c2 : C2Received) (f : Fin 262144) (s : Fin 4) :
    (helperFibres c2 f s).degree<3 := by
  have cap := helperPolynomial_degree c2 (fibreEmbed (f,s))
  have small : (helperFibres c2 f s).natDegree<3 := by
    change (helperPolynomial c2 (fibreEmbed (f,s))).natDegree<3
    omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast small)

theorem selected_overlap (S : Finset (Fin 262144)) :
    ∀ u∈code, ∀ w∈code, u≠w → (S.filter fun f => u f=w f).card≤256 := by
  intro u hu w hw different
  obtain ⟨left,rfl⟩ := hu
  obtain ⟨right,rfl⟩ := hw
  apply AspisV8.EarlyC1Identification.matching_set_cap left right
    (fun equal => different (congrArg fibreLinear equal))
  intro f hf
  exact (mem_filter.mp hf).2

/-- Literal raw and normalized-helper bad-fibre sets coincide on S. -/
theorem raw_near_helper (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (gamma : K) (nonzero : gamma≠0) (message : Message)
    (S : Finset (Fin 262144)) (B : ℕ)
    (same : ∀ f∈S, ∀ s : Fin 4, ∀ lane : Fin 26,
      received lane (fibreEmbed (f,s))=exactInitialEncoder (p lane) (fibreEmbed (f,s)))
    (near : (rawBad received c2 gamma message S).card≤B) :
    AspisV8.NearGammaDichotomy.IsNear code S (helperFibres c2) B gamma
      (fibreEncode (normalized p gamma message)) := by
  refine ⟨⟨normalized p gamma message,rfl⟩,?_⟩
  have sets : (S.filter fun f =>
      (fun s => (helperFibres c2 f s).eval gamma)≠fibreEncode (normalized p gamma message) f)=
      rawBad received c2 gamma message S := by
    ext f
    simp only [rawBad,mem_filter]
    constructor
    · rintro ⟨hf,bad⟩
      refine ⟨hf,?_⟩
      intro equal
      apply bad
      funext s
      rw [helperFibres,helperPolynomial_eval]
      apply (agreement_iff p c2 gamma nonzero message _).mp
      rw [← raw_batch_on_c1_support received p c2 gamma _ (same f hf s)]
      exact congrFun equal s
    · rintro ⟨hf,bad⟩
      refine ⟨hf,?_⟩
      intro equal
      apply bad
      funext s
      rw [raw_batch_on_c1_support received p c2 gamma _ (same f hf s)]
      apply (agreement_iff p c2 gamma nonzero message _).mpr
      simpa only [helperFibres,helperPolynomial_eval,fibreEncode] using congrFun equal s
  rw [sets]
  exact near

theorem encode_helperBatch (h : Fin 3 → Message) (gamma : K) :
    fibreLinear (helperBatch h gamma)=
      fun f s => ∑ lane : Fin 3, gamma^lane.val*fibreLinear (h lane) f s := by
  rw [helperBatch,map_sum]
  simp_rw [map_smul]
  funext f s
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- One pre-gamma helper tuple covers every later B-close original-code
message on the actual fixed support. The fewer-than-three branch remains. -/
theorem selected_cover (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (S : Finset (Fin 262144)) (G : Finset K) (B : ℕ)
    (nonzero : ∀ gamma∈G, gamma≠0)
    (same : ∀ f∈S, ∀ s : Fin 4, ∀ lane : Fin 26,
      received lane (fibreEmbed (f,s))=exactInitialEncoder (p lane) (fibreEmbed (f,s)))
    (margin : 4*B+256<S.card) :
    (goodOn c2 S B G).card<3 ∨
      ∃ h : Fin 3 → Message, ∀ gamma∈G, ∀ message : Message,
        (rawBad received c2 gamma message S).card≤B →
          message=c1Batch p gamma+gamma^26 • helperBatch h gamma := by
  rcases ThreeHelperCover.cover_dichotomy code S G (helperFibres c2) B 256
    (helper_degree c2) margin (selected_overlap S) with sparse | ⟨words,inCode,covered⟩
  · exact Or.inl sparse
  · choose h encoded using inCode
    refine Or.inr ⟨h,?_⟩
    intro gamma hg message near
    have member := raw_near_helper received p c2 gamma (nonzero gamma hg)
      message S B same near
    have wordEqual := covered gamma hg (fibreEncode (normalized p gamma message)) member
    have messageEqual : normalized p gamma message=helperBatch h gamma := by
      apply fibreEncode_injective
      rw [wordEqual]
      change _=fibreLinear (helperBatch h gamma)
      rw [encode_helperBatch]
      funext f s
      apply sum_congr rfl
      intro lane _
      rw [encoded lane]
    have scaled : gamma^26 • normalized p gamma message=message-c1Batch p gamma := by
      rw [normalized,smul_smul,mul_inv_cancel₀ (pow_ne_zero 26 (nonzero gamma hg)),one_smul]
    rw [messageEqual] at scaled
    exact (sub_eq_iff_eq_add.mp scaled.symm).trans (add_comm _ _)

/-- The unchanged optional early-C1 object supplies the fixed support and
the numerical margin. Its none branch is not asserted to satisfy this
conditional theorem. No component agreement outside its own support is used. -/
theorem early_cover (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (G : Finset K) (nonzero : ∀ gamma∈G, gamma≠0)
    (found : earlyC1 received=some p) :
    (goodOn c2 (support fibreEncode (receivedFibres received) p) 61338 G).card<3 ∨
      ∃ h : Fin 3 → Message, ∀ gamma∈G, ∀ message : Message,
        (rawBad received c2 gamma message
          (support fibreEncode (receivedFibres received) p)).card≤61338 →
          message=c1Batch p gamma+gamma^26 • helperBatch h gamma := by
  have own := some_early_has_support fibreEncode (receivedFibres received) 245609 p found
  apply selected_cover received p c2 _ G 61338 nonzero
  · intro f hf s lane
    letI : DecidablePred (fun x : Fin 262144 => ∀ column : Fin 26,
        receivedFibres received column x=fibreEncode (p column) x) :=
      fun _ => Classical.propDecidable _
    exact congrFun ((mem_filter.mp hf).2 lane) s
  · omega

#print axioms helper_degree
#print axioms selected_overlap
#print axioms raw_near_helper
#print axioms encode_helperBatch
#print axioms selected_cover
#print axioms early_cover
end
end AspisV8.ThreeHelperSelected
