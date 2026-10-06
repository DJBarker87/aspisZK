import Wide.EncoderConjugation
import Mathlib.FieldTheory.Finite.GaloisField
import WideTower

/-! Descent of exact initial codewords using the replayed distance bound.
Agreement on more than 1024 subfield-valued positions forces every conjugate
codeword to coincide with the original, hence every coordinate lies in the subfield. -/
set_option autoImplicit false
namespace AspisWide.SubfieldDescent
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.EncoderConjugation

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem initialMessage_fixed_of_agreement
    (σ : K →+* K) (received : InitialWord K) (message : InitialMessage K)
    (support : Finset (Fin 1048576)) (large : 1024 < support.card)
    (agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
    (fixed : ∀ x, σ (received x) = received x) :
    (fun i => σ (message i)) = message := by
  classical
  by_contra different
  have cap := exactInitialEncoder_overlap_cap (fun i => σ (message i)) message different
  have included : support ⊆ Finset.univ.filter (fun x =>
      exactInitialEncoder (fun i => σ (message i)) x = exactInitialEncoder message x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [map_initialEncoder]
    change σ (exactInitialEncoder message x) = exactInitialEncoder message x
    rw [agrees x hx, fixed]
  have count := Finset.card_le_card included
  change support.card ≤ agreementCount
    (exactInitialEncoder (fun i => σ (message i))) (exactInitialEncoder message) at count
  omega

theorem initialCodeword_descends
    (F : Type) [Field F] [Algebra F K]
    (received : InitialWord K) (message : InitialMessage K)
    (support : Finset (Fin 1048576)) (large : 1024 < support.card)
    (agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
    (subfieldValued : ∀ x, received x ∈ Set.range (algebraMap F K)) :
    ∀ x, exactInitialEncoder message x ∈ Set.range (algebraMap F K) := by
  intro x
  apply (IsGalois.mem_range_algebraMap_iff_fixed (exactInitialEncoder message x)).mpr
  intro σ
  have fixed : ∀ y, σ.toRingHom (received y) = received y := by
    intro y
    obtain ⟨a, ha⟩ := subfieldValued y
    rw [← ha]
    exact σ.commutes a
  have messageFixed := initialMessage_fixed_of_agreement
    σ.toRingHom received message support large agrees fixed
  have encoded := congrFun (map_initialEncoder σ.toRingHom message) x
  rw [messageFixed] at encoded
  exact encoded.symm

theorem initialCodeword_subfield_descent
    (S : Subfield K) (received : InitialWord K) (message : InitialMessage K)
    (support : Finset (Fin 1048576)) (large : 1024 < support.card)
    (agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
    (subfieldValued : ∀ x, received x ∈ S) :
    ∀ x, exactInitialEncoder message x ∈ S := by
  have descends := initialCodeword_descends S received message support large agrees
    (fun x => ⟨⟨received x, subfieldValued x⟩, rfl⟩)
  intro x
  obtain ⟨a, ha⟩ := descends x
  rw [← ha]
  exact a.property

theorem wideInitialCodeword_subfield_descent
    (S : Subfield AspisWideTower.WideExact)
    (received : InitialWord AspisWideTower.WideExact)
    (message : InitialMessage AspisWideTower.WideExact)
    (support : Finset (Fin 1048576)) (large : 1024 < support.card)
    (agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
    (subfieldValued : ∀ x, received x ∈ S) :
    ∀ x, exactInitialEncoder message x ∈ S := by
  classical
  exact initialCodeword_subfield_descent S received message support large agrees subfieldValued

#print axioms initialMessage_fixed_of_agreement
#print axioms initialCodeword_descends
#print axioms initialCodeword_subfield_descent
#print axioms wideInitialCodeword_subfield_descent
end AspisWide.SubfieldDescent
