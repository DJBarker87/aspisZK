import R0P.SemD3
import R0P.MessageDescent
import R0C.SemStatement
import R0FS.Hypotheses

/-!
G15 integration and bounded interface findings.  Lead a3c82f3d3 supplies
public-field typing and the q22 cardinality guard.  G17's proved message
descent now turns the encoder membership in `R0FS.Witness` into `BaseTyped`.
The earlier, still-valid finding helpers are retained.  No full D3 result is
claimed here.
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

/-- The opening witness's encoder descent gives exactly the message-cell
typing needed by `d3_core`, without adding a descent hypothesis. -/
theorem witness_baseTyped
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} (x : TypedContext K Sfield)
    (q : R0FS.Stmt K Sfield) (t : Trace K) (hw : R0FS.Witness q t) :
    BaseTyped x.F t := by
  intro l hl r
  exact AspisWide.SubfieldDescent.initialMessage_subfield_descent x.F (t l)
    (witness_c1_encoder_mem x q t hw l hl) r

#print axioms witness_baseTyped

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

open R0C.SemStatement

/-- `semChals` reads a semantic challenge without inspecting its message. -/
theorem semChals_head_message
    (m₁ m₂ : Msg K K (SemMsg K)) (c : K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    semChals ((m₁, Chal.semantic c) :: rest) =
      semChals ((m₂, Chal.semantic c) :: rest) := by
  rfl

#print axioms semChals_head_message

/-- Every `semPolys` lookup has offset `14+j`, so the first message is unused.
The argument is uniform in `j`; it does not enumerate the 24-round prefix. -/
theorem semPolys_head_message
    (m₁ m₂ : Msg K K (SemMsg K)) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    semPolys ((m₁, c) :: rest) = semPolys ((m₂, c) :: rest) := by
  have hindex (j : Fin 10) : 14 + j.val ≠ 0 := by omega
  by_cases hlen : rest.length + 1 = 24
  · simp only [semPolys, List.length_cons, dif_pos hlen, List.getElem_cons,
      hindex, ↓reduceDIte]
  · simp only [semPolys, List.length_cons, dif_neg hlen]

#print axioms semPolys_head_message

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The mismatched `beforeZ1`/semantic pair belongs to none of the four
current `roundBad` branches, independently of the prefix's round number. -/
theorem beforeZ1_semantic_not_roundBad {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsg K) W Sfield)
    (P : Prefix K K X (SemMsg K)) (y₀ : Fin 29 → K) (c : K) :
    ¬ R0C.SemStatement.roundBad s P (.beforeZ1 y₀) (.semantic c) := by
  intro hbad
  rcases hbad with hsem | hz₀ | hz₁ | hopen
  · obtain ⟨sm, k, _hround, hmsg, _hchal, _hbad⟩ := hsem
    cases hmsg
  · obtain ⟨y, z, _hround, hmsg, _hchal, _hbad⟩ := hz₀
    cases hmsg
  · obtain ⟨y, y₀', z₀, z₁, _hround, _hprev, _hmsg, hchal, _hbad⟩ := hz₁
    cases hchal
  · obtain ⟨Q, om, oc, _hview, hmsg, _hchal, _hround, _hbad⟩ := hopen
    cases hmsg

#print axioms beforeZ1_semantic_not_roundBad

omit [Fintype K] in
/-- The first message is outside the two-circle/opening suffix and does not
affect the semantic challenge list used by the opening view. -/
theorem openingView_first_message_eq {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (m₁ m₂ : Msg K K (SemMsg K)) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    openingView ⟨x, (m₁, c) :: rest⟩ = openingView ⟨x, (m₂, c) :: rest⟩ := by
  simp only [openingView, List.splitAt_eq, List.take_succ_cons, List.drop_succ_cons]
  generalize htail : rest.drop 23 = tail
  cases tail with
  | nil => rfl
  | cons first tail =>
    rcases first with ⟨m₀, c₀⟩
    cases m₀ <;> cases c₀ <;> try rfl
    cases tail with
    | nil => rfl
    | cons second tail =>
      rcases second with ⟨m₀, c₀⟩
      cases m₀ <;> cases c₀ <;> try rfl
      cases c <;> rfl

#print axioms openingView_first_message_eq

/-- The current decision is invariant under changing only the first message.
This is a parser equality, with no acceptance or witness premise. -/
theorem decision_first_message_eq {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (B : PackBasis F) (x : TypedContext K Sfield)
    (m₁ m₂ : Msg K K (SemMsg K)) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) (finalMsg : Msg K K (SemMsg K)) :
    SemSource.decision B ⟨x, (m₁, c) :: rest⟩ finalMsg =
      SemSource.decision B ⟨x, (m₂, c) :: rest⟩ finalMsg := by
  have hview := openingView_first_message_eq x m₁ m₂ c rest
  have hchals : semChals (((m₁, c) :: rest).take 24) =
      semChals (((m₂, c) :: rest).take 24) := by
    simp only [List.take_succ_cons]
    cases c <;> rfl
  have hpolys : semPolys (((m₁, c) :: rest).take 24) =
      semPolys (((m₂, c) :: rest).take 24) := by
    simpa only [List.take_succ_cons] using semPolys_head_message m₁ m₂ c (rest.take 23)
  unfold SemSource.decision
  rw [hview, hchals, hpolys]

#print axioms decision_first_message_eq

end
end R0P.SemD3Glue
