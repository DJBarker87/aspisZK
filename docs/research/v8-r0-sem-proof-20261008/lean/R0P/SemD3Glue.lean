import R0P.SemD3
import R0C.SemStatement
import R0FS.Hypotheses

/-!
Bounded interface findings for G15.  Lead a3c82f3d3 supplies public-field typing
and the q22 cardinality guard.  The remaining descent boundary is literal:
`R0FS.Witness` (Protocol.lean:71–74) and `AspisR0.Opening.tuple_descent`
(R0/Binding.lean:105–115) type `exactInitialEncoder (t l) i`, whereas
`BaseTyped` types the message cells `t l b`.  The theorem below records exactly
what `Witness` and `TypedContext.lanesF` yield.  No message-descent premise or
full D3 result is installed.  The two earlier, still-valid finding helpers are
retained; the old untyped-context counterexample is superseded by `pubBase`.
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

/-- Witness descent gives base-typed C1 *codeword* coordinates.  Its index is
`Fin 1048576`, not the `Fin 1024` index of the candidate message cells. -/
theorem witness_c1_encoder_mem
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} (x : TypedContext K Sfield)
    (q : R0FS.Stmt K Sfield) (t : Trace K) (hw : R0FS.Witness q t)
    (l : Fin 29) (hl : l.val < 26) (i : Fin 1048576) :
    AspisWide.InitialEncoder.exactInitialEncoder (t l) i ∈ x.F := by
  rw [← x.lanesF l hl]
  exact hw.2.2 l i

#print axioms witness_c1_encoder_mem

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
