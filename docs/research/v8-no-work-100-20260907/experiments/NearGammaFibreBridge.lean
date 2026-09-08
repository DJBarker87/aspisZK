import AspisFormal.Pool.V7FixedWidth29TupleList
import AspisFormal.V5FriRelationCandidateBridge

/-! The actual fibre-major map turns each complete V8 four-slot agreement
into four distinct initial-code symbol agreements. -/
set_option autoImplicit false
namespace AspisV8.NearGammaFibreBridge
open Finset
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriRelationCandidateBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact

def fibreEmbed : Fin 262144 × Fin 4 ↪ Fin 1048576 where
  toFun pair := ⟨4*pair.1.val+pair.2.val, by omega⟩
  inj' := by
    intro a b h
    apply Prod.ext
    · apply Fin.ext
      have hv := Fin.mk.inj_iff.mp h
      omega
    · apply Fin.ext
      have hv := Fin.mk.inj_iff.mp h
      omega

theorem fibreEmbed_eq_source (fibre : Fin 262144) (slot : Fin 4) :
    fibreEmbed (fibre,slot) = fibreSlotEquiv 262144 (fibre,slot) := by
  rw [fibreSlotEquiv_apply]
  apply Fin.ext
  simp [fibreEmbed, childIndex]

def fibreAgreement {V : Type*} [DecidableEq V]
    (left right : Fin 1048576 → V) : Finset (Fin 262144) :=
  Finset.univ.filter fun fibre => ∀ slot : Fin 4,
    left (fibreEmbed (fibre,slot)) = right (fibreEmbed (fibre,slot))

theorem fibre_card_bound {V F S I : Type*} [DecidableEq V]
    [Fintype F] [Fintype S] [Fintype I]
    [DecidableEq F] [DecidableEq S] [DecidableEq I]
    (emb : F × S ↪ I) (left right : I → V) (Good : Finset F)
    (hmatches : ∀ f ∈ Good, ∀ s, left (emb (f,s)) = right (emb (f,s))) :
    Fintype.card S * Good.card ≤
    (Finset.univ.filter fun i => left i = right i).card := by
  classical
  let P := Good.product (Finset.univ : Finset S)
  have subset : P.map emb ⊆ Finset.univ.filter fun index =>
      left index = right index := by
    intro index hi
    obtain ⟨pair,hpair,hindex⟩ := Finset.mem_map.mp hi
    obtain ⟨hf,hs⟩ := Finset.mem_product.mp hpair
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hindex]
    exact hmatches pair.1 hf pair.2
  calc
    Fintype.card S * Good.card = P.card := by simp [P, Nat.mul_comm]
    _ = (P.map emb).card := by simp only [card_map]
    _ ≤ _ := Finset.card_le_card subset

theorem fibre_overlap_le_256 {V : Type*} [DecidableEq V]
    (left right : Fin 1048576 → V)
    (symbolCap : (Finset.univ.filter fun i => left i = right i).card ≤ 1024) :
    (fibreAgreement left right).card ≤ 256 := by
  have count := (fibre_card_bound fibreEmbed left right (fibreAgreement left right)
    (fun f hf s => (Finset.mem_filter.mp hf).2 s)).trans symbolCap
  rw [Fintype.card_fin] at count
  omega

noncomputable def fullFibreAgreement (left right : InitialMessage QM31Exact) :
    Finset (Fin 262144) := fibreAgreement (exactInitialEncoder left) (exactInitialEncoder right)

theorem full_fibre_overlap_le_256 (left right : InitialMessage QM31Exact)
    (different : left ≠ right) :
    (fullFibreAgreement left right).card ≤ 256 := by
  apply fibre_overlap_le_256
  simpa [AspisPool.AlgorithmicCircleDecoderV7.agreementCount] using
    exactInitialEncoder_overlap_cap left right different

#print axioms full_fibre_overlap_le_256
#print axioms fibre_overlap_le_256
#print axioms fibreEmbed_eq_source
end AspisV8.NearGammaFibreBridge
