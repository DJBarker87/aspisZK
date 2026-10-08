import R0P.SemD2
import R0P.MessageDescent
import R0C.SemStatement
import R0FS.Hypotheses

/-!
G15 integration and bounded interface findings.  Lead a3c82f3d3 supplies
public-field typing and the q22 cardinality guard.  G17's proved message
descent now turns the encoder membership in `R0FS.Witness` into `BaseTyped`.
The earlier tag-invariance findings are superseded by lead 84a2dce11 and
removed: semantic parsing now requires semantic message tags and the C2
commitment.  The remaining integration uses the prefix-based `semanticBad`.
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

/-- The pair-forest B2 operations, using the lead's literal prefix classifier. -/
def sourceData [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} {F : Subfield K} (B : PackBasis F) :
    R0C.SemStatement.SourceData (K := K) (E := K)
      (TypedContext K Sfield) (SemMsg K) (Trace K) Sfield where
  semanticRounds := 24
  semanticBad := SemSource.semanticBad B
  paymentWitness := fun x t => InputNoteExtracted x.pub t
  openingView := SemSource.openingView
  decision := SemSource.decision B

#print axioms sourceData

/-- Forget the duplex state while retaining every message and challenge value. -/
def valuePrefix {X M C S : Type} (p : FS.Prefix X M (C × S)) : FS.Prefix X M C :=
  ⟨p.statement, p.rounds.map (fun r => (r.1, r.2.1))⟩

#print axioms valuePrefix

theorem valuePrefix_ext {X M C S : Type} (p : FS.Prefix X M (C × S))
    (m : M) (c : C × S) :
    valuePrefix (p.ext m c) = (valuePrefix p).ext m c.1 := by
  simp only [valuePrefix, FS.Prefix.ext, List.map_append, List.map_singleton]

#print axioms valuePrefix_ext

theorem valuePrefix_round {X M C S : Type} (p : FS.Prefix X M (C × S)) :
    (valuePrefix p).round = p.round := by
  simp only [valuePrefix, FS.Prefix.round, List.length_map]

#print axioms valuePrefix_round

/-- The B2 state predicate on a transcript that also retains sampler state.
The error schedule is data: D3 depends only on the doomed predicate. -/
def duplexRows [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} {F : Subfield K} (B : PackBasis F)
    {S I A : Type} (budget : Nat → ℚ) :
    FS2.RoundByRound' (TypedContext K Sfield) (R0C.SemStatement.Msg K K (SemMsg K))
      (R0C.SemStatement.Chal K K × S) I A where
  doomed := fun p table => R0C.SemStatement.doomed (sourceData B) (valuePrefix p) table
  ε := budget

#print axioms duplexRows

open R0C.SemStatement Polynomial

theorem semChals_semantic_head (sm₁ sm₂ : SemMsg K) (c : K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    semChals ((Msg.semantic sm₁, Chal.semantic c) :: rest) =
      semChals ((Msg.semantic sm₂, Chal.semantic c) :: rest) := by
  rfl

#print axioms semChals_semantic_head

/-- The C2 parser reads index 2, independently of the first inner payload. -/
theorem c2Of_head (sm₁ sm₂ : SemMsg K) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    c2Of ((Msg.semantic sm₁, c) :: rest) =
      c2Of ((Msg.semantic sm₂, c) :: rest) := by
  rfl

#print axioms c2Of_head

theorem semPolys_semantic_head (sm₁ sm₂ : SemMsg K) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    semPolys ((Msg.semantic sm₁, c) :: rest) =
      semPolys ((Msg.semantic sm₂, c) :: rest) := by
  have hindex (j : Fin 10) : 14 + j.val ≠ 0 := by omega
  by_cases hlen : rest.length + 1 = 24
  · simp only [semPolys, List.length_cons, dif_pos hlen, List.getElem_cons,
      hindex, ↓reduceDIte]
  · simp only [semPolys, List.length_cons, dif_neg hlen]

#print axioms semPolys_semantic_head

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

omit [Fintype K] in
theorem openingView_semantic_head {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (sm₁ sm₂ : SemMsg K) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) :
    openingView ⟨x, (Msg.semantic sm₁, c) :: rest⟩ =
      openingView ⟨x, (Msg.semantic sm₂, c) :: rest⟩ := by
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

#print axioms openingView_semantic_head

theorem decision_semantic_head {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (B : PackBasis F) (x : TypedContext K Sfield) (sm₁ sm₂ : SemMsg K) (c : Chal K K)
    (rest : List (Msg K K (SemMsg K) × Chal K K)) (finalMsg : Msg K K (SemMsg K)) :
    SemSource.decision B ⟨x, (Msg.semantic sm₁, c) :: rest⟩ finalMsg =
      SemSource.decision B ⟨x, (Msg.semantic sm₂, c) :: rest⟩ finalMsg := by
  have hview := openingView_semantic_head x sm₁ sm₂ c rest
  have hchals : semChals (((Msg.semantic sm₁, c) :: rest).take 24) =
      semChals (((Msg.semantic sm₂, c) :: rest).take 24) := by
    simp only [List.take_succ_cons]
    cases c <;> rfl
  have hpolys : semPolys (((Msg.semantic sm₁, c) :: rest).take 24) =
      semPolys (((Msg.semantic sm₂, c) :: rest).take 24) := by
    simpa only [List.take_succ_cons] using semPolys_semantic_head sm₁ sm₂ c (rest.take 23)
  unfold SemSource.decision
  rw [hview, hchals, hpolys]

#print axioms decision_semantic_head

/-- The current semantic classifier suppresses every event for a high-degree
roundPoly payload, even when the current round is before the alpha rounds. -/
theorem semanticBad_roundPoly_high_false {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (B : PackBasis F) (P : Prefix K K (TypedContext K Sfield) (SemMsg K))
    (p : K[X]) (hp : 27 < p.natDegree) (c : K) :
    ¬ semanticBad B P (.roundPoly p) c := by
  rintro ⟨_hlen, _cs, _hparse, hdeg, _hrest⟩
  change p.natDegree ≤ 27 at hdeg
  exact (Nat.not_le_of_gt hp) hdeg

#print axioms semanticBad_roundPoly_high_false

/-- A concrete inner semantic payload that suppresses the current bad event;
the degree calculation is symbolic and uses no trace or field enumeration. -/
theorem semanticBad_X28_false {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (B : PackBasis F) (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) (c : K) :
    ¬ semanticBad B P (.roundPoly ((X : K[X]) ^ 28)) c := by
  apply semanticBad_roundPoly_high_false B P _ _ c
  rw [Polynomial.natDegree_X_pow]
  omega

#print axioms semanticBad_X28_false

end
end R0P.SemD3Glue
