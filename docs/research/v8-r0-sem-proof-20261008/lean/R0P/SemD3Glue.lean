import R0P.SemD3
import R0C.SemStatement
import R0FS.Hypotheses

/-!
Bounded interface findings for G15.  These facts identify missing hypotheses in
the current abstraction; they do not claim that the full D3 statement is false.
In particular, `d3_core` requires `PublicBase`, while `TypedContext` contains no
such field.  The old opening theorem `accept_not_doomed` requires nonzero gamma
and a 22-element query set; the old protocol D3 obtains those from
`SamplerLaws.nonzero` and `SamplerLaws.queryCard`, neither of which is part of
B2 `SourceData`.
-/
set_option autoImplicit false
namespace R0P.SemD3Glue

open R0P R0P.SemSource R0FS

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K]

/-- A packed basis vector `i` cannot itself belong to the base subfield. -/
theorem packBasis_i_not_mem {F : Subfield K} (B : PackBasis F) : B.i ∉ F := by
  intro hi
  have h := B.indep (-B.i) 1 0 0 (Subfield.neg_mem F hi) (one_mem F)
    (zero_mem F) (zero_mem F) (by ring)
  exact one_ne_zero h.2.1

#print axioms packBasis_i_not_mem

/-- An arbitrary public record can be placed in a `TypedContext` with zero
words while violating `PublicBase`, by setting `assetId` to the basis element.
This witnesses why `TypedContext`'s word typing alone cannot discharge the
`hpub` argument required by `d3_core`. -/
theorem exists_zero_context_not_publicBase
    {Sfield : Fin 29 → Subfield K} (F : Subfield K) (B : PackBasis F)
    (pub : Public K) :
    ∃ x : TypedContext K Sfield,
      x.W = (fun _ _ => (0 : K)) ∧ x.pub.assetId = B.i ∧ ¬ PublicBase F x.pub := by
  let x : TypedContext K Sfield :=
    { pub := { pub with assetId := B.i }
      W := fun _ _ => (0 : K)
      base := fun l _ => zero_mem (Sfield l) }
  refine ⟨x, rfl, rfl, ?_⟩
  intro hpub
  have hi : B.i ∈ F := by simpa [x] using hpub.2.2.1
  exact packBasis_i_not_mem B hi

#print axioms exists_zero_context_not_publicBase

/-- The `bad4` condition cannot hold for an empty query set because it requires
exactly 22 queries. -/
theorem bad4_empty_false
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} (x : R0FS.Stmt K Sfield)
    (y : Fin 29 → Fin 2 → K) (γ α : K)
    (F : AspisPool.AlgorithmicCircleDecoderV7.FinalMessage K) :
    ¬ R0FS.bad4 x y γ α F ∅ := by
  intro h
  have h22 : (∅ : Finset (Fin 262144)).card = 22 := h.2.1
  simp at h22

#print axioms bad4_empty_false

end
end R0P.SemD3Glue
