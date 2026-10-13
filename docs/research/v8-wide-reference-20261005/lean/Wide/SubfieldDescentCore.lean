import Wide.EncoderConjugation
import Mathlib.FieldTheory.Finite.GaloisField

/-! Descent of exact initial codewords using the replayed distance bound.
Agreement on more than 1024 subfield-valued positions forces every conjugate
codeword to coincide with the original. These unchanged generic theorems are
separated from the concrete WideExact specialization to keep the import small. -/
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

/-- If every exact encoder coordinate lies in `S`, then every coordinate of
the initial message itself lies in `S`. -/
theorem initialMessage_subfield_descent
    (S : Subfield K) (m : InitialMessage K)
    (h : ∀ x, exactInitialEncoder m x ∈ S) :
    ∀ r, m r ∈ S := by
  have hlarge : 1024 < (Finset.univ : Finset (Fin 1048576)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    norm_num
  intro r
  have hrange : m r ∈ Set.range (algebraMap S K) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (m r)).mpr
    intro σ
    have messageFixed : (fun i => σ.toRingHom (m i)) = m :=
      initialMessage_fixed_of_agreement σ.toRingHom (exactInitialEncoder m) m
        Finset.univ hlarge (by intro i _; rfl) (by
          intro i
          have hsub : exactInitialEncoder m i ∈ Set.range (algebraMap S K) :=
            ⟨⟨exactInitialEncoder m i, h i⟩, rfl⟩
          obtain ⟨a, ha⟩ := hsub
          rw [← ha]
          exact σ.commutes a)
    exact congrFun messageFixed r
  obtain ⟨a, ha⟩ := hrange
  rw [← ha]
  exact a.property

#print axioms initialMessage_fixed_of_agreement
#print axioms initialCodeword_descends
#print axioms initialCodeword_subfield_descent
#print axioms initialMessage_subfield_descent
end AspisWide.SubfieldDescent
