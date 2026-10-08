import Wide.InitialEncoder
import Wide.SubfieldDescent
import Wide.EncoderLinearity
import Mathlib

/-! Generic message-cell descent from subfield-valued exact encoder cells.
The proof uses the existing automorphism fixedness lemma on the full encoder
support and the fixed-field characterization for finite field extensions. -/
set_option autoImplicit false
namespace AspisWide.SubfieldDescent

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

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

#print axioms initialMessage_subfield_descent

end AspisWide.SubfieldDescent
