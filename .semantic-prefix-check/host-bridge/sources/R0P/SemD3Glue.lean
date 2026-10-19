import R0P.SemD2
import R0P.CircleSampler
import R0P.SemAccept
import R0P.SemHonest
import R0P.SemVirtualDeg
import R0P.SemPad
import R0C.V3.R0Q
import R0P.MessageDescent
import R0C.SemStatement
import R0FS.Hypotheses

/-!
G15 integration and parser bridges.  Lead a3c82f3d3 supplies
public-field typing and the q22 cardinality guard.  G17's proved message
descent now turns the encoder membership in `R0FS.Witness` into `BaseTyped`.
The earlier tag-invariance findings are superseded by lead 84a2dce11 and
removed: semantic parsing now requires semantic message tags and the C2
commitment.  Lead 7d3aa4864 restricts the degree guard to the alpha phase;
the superseded unconditional-guard findings are removed.  The integration
uses the literal prefix-based `semanticBad`.

The final `d3` discharges the three G14 bridges with SemHonest,
SemVirtualDeg, and SemAccept. It proves the fixed D3 component without
adding semantic premises to `SemStatement.Obligations`.
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
  exact hw.2.2.2 l i

#print axioms witness_c1_encoder_mem

/-- The opening witness's encoder descent gives exactly the message-cell
typing needed by `d3_core`, without adding a descent hypothesis. -/
theorem witness_baseTyped
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    {Sfield : Fin 29 → Subfield K} (x : TypedContext K Sfield)
    (q : R0FS.Stmt K Sfield) (t : Trace K) (hw : R0FS.Witness q (coeffsOf x.transport t)) :
    BaseTyped x.F t := by
  intro l hl r
  simpa only [coeffsOf, Equiv.symm_apply_apply] using
    AspisWide.SubfieldDescent.initialMessage_subfield_descent x.F (coeffsOf x.transport t l)
    (witness_c1_encoder_mem x q (coeffsOf x.transport t) hw l hl) (x.transport r)

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

/-- Generic source operations with the reserved fallback supplied as data. -/
def sourceDataWithFallback [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (fallback1 : AspisR0.ChordGeometry.Point K)
    {Sfield : Fin 29 → Subfield K} {F : Subfield K} (B : PackBasis F) :
    R0C.SemStatement.SourceData (K := K) (E := K)
      (TypedContext K Sfield) (SemMsg K) (Trace K) Sfield where
  semanticRounds := 24
  circleFallback1 := fallback1
  semanticBad := SemSource.semanticBad B
  paymentWitness := fun x t => InputNoteExtracted x.pub t
  openingView := SemSource.openingView
  decision := SemSource.decision B

/-- The concrete source fixes the second-row fallback to the checked G22 point. -/
def sourceData {Sfield : Fin 29 → Subfield AspisWideTower.WideExact}
    {F : Subfield AspisWideTower.WideExact} (B : PackBasis F) :
    R0C.SemStatement.SourceData (K := AspisWideTower.WideExact) (E := AspisWideTower.WideExact)
      (TypedContext AspisWideTower.WideExact Sfield) (SemMsg AspisWideTower.WideExact)
      (Trace AspisWideTower.WideExact) Sfield where
  semanticRounds := 24
  circleFallback1 := R0P.SemSource.circleFallback1
  semanticBad := SemSource.semanticBad B
  paymentWitness := fun x t => InputNoteExtracted x.pub t
  openingView := SemSource.openingView
  decision := SemSource.decision B

#print axioms sourceDataWithFallback
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
def duplexRows
    {Sfield : Fin 29 → Subfield AspisWideTower.WideExact}
    {F : Subfield AspisWideTower.WideExact} (B : PackBasis F)
    {S I A : Type} (budget : Nat → ℚ) :
    FS2.RoundByRound' (TypedContext AspisWideTower.WideExact Sfield)
      (R0C.SemStatement.Msg AspisWideTower.WideExact AspisWideTower.WideExact
        (SemMsg AspisWideTower.WideExact))
      (R0C.SemStatement.Chal AspisWideTower.WideExact AspisWideTower.WideExact × S) I A where
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

end
end R0P.SemD3Glue

noncomputable section
namespace R0P.SemD3Glue
open R0P.SemSource R0C.SemStatement
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.Chord AspisR0.ChordGeometry

variable {K : Type} [Field K]

theorem semChals_of_pairs (rs : List (SemMsg K × K)) :
    semChals (rs.map (fun q => (Msg.semantic q.1, Chal.semantic q.2))) =
      some (rs.map Prod.snd) := by
  induction rs with
  | nil => rfl
  | cons q rs ih =>
      rcases q with ⟨m, c⟩
      simp only [List.map_cons, semChals, ih, Option.map_some]

#print axioms semChals_of_pairs

theorem semChals_some_structure
    (rounds : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
    (h : semChals rounds = some cs) :
    ∃ rs : List (SemMsg K × K),
      rounds = rs.map (fun q => (Msg.semantic q.1, Chal.semantic q.2)) ∧
      cs = rs.map Prod.snd := by
  induction rounds generalizing cs with
  | nil =>
      have hc : cs = [] := Option.some.inj h.symm
      exact ⟨[], rfl, hc⟩
  | cons q rounds ih =>
      rcases q with ⟨m, c⟩
      cases m <;> cases c <;> simp [semChals] at h
      rename_i sm c
      obtain ⟨tail, htail, rfl⟩ := h
      obtain ⟨rs, hrs, hcs⟩ := ih tail htail
      exact ⟨(sm, c) :: rs, by simp only [List.map_cons, hrs],
        by simp only [List.map_cons, hcs]⟩

#print axioms semChals_some_structure

theorem semChals_length
    (rounds : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
    (h : semChals rounds = some cs) : cs.length = rounds.length := by
  obtain ⟨rs, rfl, rfl⟩ := semChals_some_structure rounds cs h
  simp only [List.length_map]

#print axioms semChals_length

theorem semChals_take
    (rounds : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
    (h : semChals rounds = some cs) (n : Nat) :
    semChals (rounds.take n) = some (cs.take n) := by
  obtain ⟨rs, rfl, rfl⟩ := semChals_some_structure rounds cs h
  simp only [← List.map_take]
  exact semChals_of_pairs (rs.take n)

#print axioms semChals_take

theorem semChals_getElem
    (rounds : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
    (h : semChals rounds = some cs) (i : Fin rounds.length) :
    ∃ sm : SemMsg K, rounds[i.val] =
      (Msg.semantic sm, Chal.semantic (cs[i.val]'(by
        have hlen := semChals_length rounds cs h
        omega))) := by
  obtain ⟨rs, rfl, rfl⟩ := semChals_some_structure rounds cs h
  have hi : i.val < rs.length := by simpa only [List.length_map] using i.isLt
  refine ⟨(rs[i.val]'hi).1, ?_⟩
  simp only [List.getElem_map]

#print axioms semChals_getElem

def openingPairs (os : List (R0FS.Msg K × R0FS.Chal K)) :
    List (Msg K K (SemMsg K) × Chal K K) :=
  os.map (fun q => (Msg.opening q.1, Chal.opening q.2))

#print axioms openingPairs

theorem openingRounds_pairs (os : List (R0FS.Msg K × R0FS.Chal K)) :
    openingRounds (openingPairs os) = some os := by
  induction os with
  | nil => rfl
  | cons q os ih =>
      rcases q with ⟨m, c⟩
      simp only [openingPairs, List.map_cons, openingRounds] at ih ⊢
      rw [ih]
      rfl

#print axioms openingRounds_pairs

theorem openingRounds_some
    (rounds : List (Msg K K (SemMsg K) × Chal K K))
    (os : List (R0FS.Msg K × R0FS.Chal K))
    (h : openingRounds rounds = some os) : rounds = openingPairs os := by
  induction rounds generalizing os with
  | nil =>
      have hos : os = [] := Option.some.inj h.symm
      subst os
      rfl
  | cons q rounds ih =>
      rcases q with ⟨m, c⟩
      cases m <;> cases c <;> simp [openingRounds] at h
      rename_i om oc
      obtain ⟨tail, htail, rfl⟩ := h
      have ht := ih tail htail
      simpa only [openingPairs, List.map_cons] using
        congrArg (List.cons (Msg.opening om, Chal.opening oc)) ht

#print axioms openingRounds_some

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

omit [Fintype K] in
theorem openingView_of_parsed {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield)
    (sem : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
    (hsem : sem.length = 24) (hcs : cs.length = 24)
    (hparse : semChals sem = some cs)
    (hw gw : InitialWord K) (hc2 : c2Of sem = some (hw, gw))
    (hb : c2Base Sfield hw gw)
    (y : Fin 3 → Fin 29 → K) (y₀ : Fin 29 → K) (z₀ z₁ : Point K)
    (hne : z₀ ≠ z₁) (h₀ : ¬ BaseRational z₀) (h₁ : ¬ BaseRational z₁)
    (os : List (R0FS.Msg K × R0FS.Chal K)) :
    openingView ⟨x, sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairs os)⟩ =
      some ⟨openingStmt x hw gw hb (fun j => cs[14 + j.val]'(by omega))
        y z₀ z₁ hne h₀ h₁, os⟩ := by
  unfold openingView
  rw [List.splitAt_eq]
  have htake : (sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairs os)).take 24 = sem := by
    rw [← hsem]
    exact List.take_left
  have hdrop : (sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairs os)).drop 24 =
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairs os) := by
    rw [← hsem]
    exact List.drop_left
  rw [htake, hdrop]
  simp only [hparse, hc2, openingRounds_pairs]
  rw [dif_pos ⟨hcs, hb, hne, h₀, h₁⟩]

#print axioms openingView_of_parsed

omit [Fintype K] in
theorem openingView_some_structure {Sfield : Fin 29 → Subfield K}
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingView P = some Q) :
    ∃ (sem : List (Msg K K (SemMsg K) × Chal K K)) (cs : List K)
      (hw gw : InitialWord K) (y : Fin 3 → Fin 29 → K) (y₀ : Fin 29 → K)
      (z₀ z₁ : Point K) (hcs : cs.length = 24) (hb : c2Base Sfield hw gw)
      (hne : z₀ ≠ z₁) (h₀ : ¬ BaseRational z₀) (h₁ : ¬ BaseRational z₁)
      (os : List (R0FS.Msg K × R0FS.Chal K)),
      sem.length = 24 ∧ semChals sem = some cs ∧ c2Of sem = some (hw, gw) ∧
      P.rounds = sem ++
        ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairs os) ∧
      Q = ⟨openingStmt P.statement hw gw hb (fun j => cs[14 + j.val]'(by omega))
        y z₀ z₁ hne h₀ h₁, os⟩ := by
  cases hsplit : P.rounds.splitAt 24 with
  | mk sem suffix =>
      cases suffix with
      | nil =>
          simp only [openingView, hsplit] at hview
          cases hview
      | cons first suffix =>
          rcases first with ⟨m₀, c₀⟩
          cases m₀ <;> cases c₀ <;> simp only [openingView, hsplit] at hview
          all_goals try contradiction
          rename_i y z₀
          cases suffix with
          | nil => simp at hview
          | cons second opening =>
              rcases second with ⟨m₁, c₁⟩
              cases m₁ <;> cases c₁ <;> simp only at hview
              all_goals try contradiction
              rename_i y₀ z₁
              cases hparse : semChals sem with
              | none => simp only [hparse] at hview; contradiction
              | some cs =>
                  cases hc2 : c2Of sem with
                  | none => simp only [hparse, hc2] at hview; contradiction
                  | some words =>
                      rcases words with ⟨hw, gw⟩
                      cases hopen : openingRounds opening with
                      | none => simp only [hparse, hc2, hopen] at hview; contradiction
                      | some os =>
                          simp only [hparse, hc2, hopen] at hview
                          split at hview
                          · rename_i hvalid
                            have hQ := Option.some.inj hview
                            have hlen : sem.length = 24 :=
                              (semChals_length sem cs hparse).symm.trans hvalid.1
                            have hrounds : P.rounds = sem ++
                                ((Msg.beforeZ0 y, Chal.circle z₀) ::
                                  (Msg.beforeZ1 y₀, Chal.circle z₁) :: opening) := by
                              have hs := congrArg (fun q => q.1 ++ q.2) hsplit
                              simpa only [List.splitAt_eq, List.take_append_drop] using hs
                            refine ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hvalid.1,
                              hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1, hvalid.2.2.2.2,
                              os, hlen, hparse, hc2, ?_, hQ.symm⟩
                            rw [openingRounds_some opening os hopen] at hrounds
                            exact hrounds
                          · contradiction

#print axioms openingView_some_structure

theorem hitFrom_suffix {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsg K) W Sfield) (x : X) :
    ∀ (front tail prev : List (Msg K K (SemMsg K) × Chal K K)),
      hitFrom s x (prev ++ front) tail → hitFrom s x prev (front ++ tail) := by
  intro front
  induction front with
  | nil =>
      intro tail prev h
      simpa only [List.append_nil, List.nil_append] using h
  | cons q front ih =>
      intro tail prev h
      rcases q with ⟨m, c⟩
      apply Or.inr
      apply ih tail (prev ++ [(m, c)])
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

#print axioms hitFrom_suffix

theorem opening_goodFrom_hitFrom {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsg K) W Sfield) (x : X)
    (base : List (Msg K K (SemMsg K) × Chal K K)) (stmt : R0FS.Stmt K Sfield)
    (hbase : base.length = s.semanticRounds + 2)
    (hview : ∀ prev, s.openingView ⟨x, base ++ openingPairs prev⟩ = some ⟨stmt, prev⟩) :
    ∀ (rest prev : List (R0FS.Msg K × R0FS.Chal K)),
      R0FS.goodFrom stmt prev rest →
        hitFrom s x (base ++ openingPairs prev) (openingPairs rest) := by
  intro rest
  induction rest with
  | nil =>
      intro prev h
      exact False.elim h
  | cons q rest ih =>
      intro prev h
      rcases q with ⟨m, c⟩
      change R0FS.roundBad stmt prev m c ∨
        R0FS.goodFrom stmt (prev ++ [(m, c)]) rest at h
      change roundBad s ⟨x, base ++ openingPairs prev⟩ (.opening m) (.opening c) ∨
        hitFrom s x ((base ++ openingPairs prev) ++ [(.opening m, .opening c)])
          (openingPairs rest)
      rcases h with hbad | htail
      · left
        apply Or.inr
        apply Or.inr
        apply Or.inr
        refine ⟨⟨stmt, prev⟩, m, c, hview prev, rfl, rfl, ?_, hbad⟩
        simp only [FS.Prefix.round, List.length_append, openingPairs, List.length_map, hbase]
      · right
        have ht := ih (prev ++ [(m, c)]) htail
        simpa only [openingPairs, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc] using ht

#print axioms opening_goodFrom_hitFrom

theorem opening_good_hitFrom {W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) (TypedContext K Sfield) (SemMsg K) W Sfield)
    (hsview : s.openingView = openingView) (hsrounds : s.semanticRounds = 24)
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingView P = some Q) (hgood : R0FS.good Q.statement Q.rounds) :
    hitFrom s P.statement [] P.rounds := by
  obtain ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hcs, hb, hne, h₀, h₁, os,
    hsem, hparse, hc2, hrounds, hQ⟩ := openingView_some_structure P Q hview
  subst Q
  let base := sem ++ [(Msg.beforeZ0 y, Chal.circle z₀), (Msg.beforeZ1 y₀, Chal.circle z₁)]
  let stmt := openingStmt P.statement hw gw hb (fun j => cs[14 + j.val]'(by omega))
    y z₀ z₁ hne h₀ h₁
  have hbase : base.length = s.semanticRounds + 2 := by
    simp only [base, List.length_append, List.length_cons, List.length_nil, hsem, hsrounds]
  have hprefix : ∀ prev, s.openingView ⟨P.statement, base ++ openingPairs prev⟩ =
      some ⟨stmt, prev⟩ := by
    intro prev
    rw [hsview]
    simpa only [base, stmt, List.append_assoc, List.cons_append, List.nil_append] using
      openingView_of_parsed P.statement sem cs hsem hcs hparse hw gw hc2 hb
        y y₀ z₀ z₁ hne h₀ h₁ prev
  have htail := opening_goodFrom_hitFrom s P.statement base stmt hbase hprefix os [] hgood
  have htail' : hitFrom s P.statement ([] ++ base) (openingPairs os) := by
    simpa only [openingPairs, List.map_nil, List.append_nil, List.nil_append] using htail
  have hall := hitFrom_suffix s P.statement base (openingPairs os) [] htail'
  rw [hrounds]
  simpa only [base, List.append_assoc, List.cons_append, List.nil_append] using hall

#print axioms opening_good_hitFrom

end R0P.SemD3Glue
end

namespace R0P.SemD3Glue
open FS FS2 FS2.Duplex R0C.SemStatement R0P.SemSource
open AspisWideTower AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
abbrev SemE := WideExact
#print axioms SemE

/-- The existing opening sampler's parameters, with the semantic protocol's
message encoding and labels shifted to rounds 26--30. -/
def openingParams {L : Nat}
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (s : State) : Duplex.Params (R0FS.Msg SemE) (R0FS.Chal SemE) L where
  D := p.D
  hL := p.hL
  enc := fun m => p.enc (.opening m)
  encLen := fun m => p.encLen (.opening m)
  dec := fun bytes => match p.dec bytes with
    | some (.opening m) => some m
    | _ => none
  decEnc := fun m => by rw [p.decEnc]
  lbl := fun j => p.lbl (26 + j)
  σ := R0C.V3.DQ.σQ
  iv := s
  rounds := 5

#print axioms openingParams

/-- Lift an opening challenge and its retained duplex state. -/
def openingChallenge (c : R0C.V3.DQ.DC) : Duplex.Chal (Chal SemE SemE) :=
  (.opening c.1, c.2)

#print axioms openingChallenge

/-- The mixed protocol's first thirty rows use one absorb/squeeze/advance
block. The final row is literally the q22 sampler's eight-pair chain,
with the full mixed-prefix state, message encoding and label. -/
def combinedSampler {X : Type} {L : Nat}
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (i : Nat) (P : FS.Prefix X (Msg SemE SemE (SemMsg SemE))
      (Duplex.Chal (Chal SemE SemE))) (m : Msg SemE SemE (SemMsg SemE)) :
    FS2.Sampler (Addr L) State (Duplex.Chal (Chal SemE SemE)) :=
  if i < 30 then Duplex.samp p i P m
  else .ask (absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)) fun s' =>
    R0C.V3.DQ.chainS (openingParams p s')
      (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []

#print axioms combinedSampler
end
end R0P.SemD3Glue

namespace R0P.SemD3Glue
open R0P R0P.SemSource R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda LambdaRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Any selected bad round is a hit in the containing transcript. -/
theorem roundBad_hitFrom {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsg K) W Sfield) (x : X) :
    ∀ (rs prev : List (Msg K K (SemMsg K) × Chal K K)) (i : Nat) (hi : i < rs.length),
      roundBad s ⟨x, prev ++ rs.take i⟩ (rs[i]'hi).1 (rs[i]'hi).2 →
        hitFrom s x prev rs := by
  intro rs
  induction rs with
  | nil => intro prev i hi; simp at hi
  | cons q rs ih =>
      intro prev i hi hbad
      rcases q with ⟨m,c⟩
      cases i with
      | zero =>
          left
          simpa only [List.take_zero, List.append_nil, List.getElem_cons_zero] using hbad
      | succ i =>
          right
          apply ih (prev ++ [(m,c)]) i (by simp only [List.length_cons] at hi; omega)
          simpa only [List.take_succ_cons, List.getElem_cons_succ, List.append_assoc,
            List.singleton_append] using hbad

#print axioms roundBad_hitFrom

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- An initial segment retains the already committed C2 words. -/
theorem c2Of_take (rs : List (Msg K K (SemMsg K) × Chal K K)) (n : Nat) (hn : 2 < n) :
    c2Of (rs.take n) = c2Of rs := by
  simp only [c2Of, List.getElem?_take_of_lt hn]

#print axioms c2Of_take

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- A successful C2 parse determines exactly the current commitment message. -/
theorem c2Of_getElem (rs : List (Msg K K (SemMsg K) × Chal K K))
    (hw gw : InitialWord K) (hlen : 2 < rs.length) (hc2 : c2Of rs = some (hw,gw)) :
    (rs[2]'hlen).1 = .semantic (.h1 hw gw) := by
  rcases he : rs[2]'hlen with ⟨m,c⟩
  have hp := hc2
  simp only [c2Of, List.getElem?_eq_getElem hlen, he] at hp
  cases m with
  | semantic sm =>
      cases sm with
      | none => cases hp
      | roundPoly p => cases hp
      | h1 h g =>
          have hwords := Option.some.inj hp
          cases hwords
          rfl
  | beforeZ0 y => cases hp
  | beforeZ1 y => cases hp
  | opening om => cases hp

#print axioms c2Of_getElem

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- The literal bad-round classifier does not inspect the strategy before alpha. -/
theorem semRoundBad_strat_early {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (s₁ s₂ : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K) (c : K) (hi : i.val < 14) :
    semRoundBad t pub B G s₁ i pref c ↔ semRoundBad t pub B G s₂ i pref c := by
  unfold semRoundBad
  split_ifs with h0 h1 h2 hz hm <;> try rfl
  omega

#print axioms semRoundBad_strat_early

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- Before the C2 commitment only lambda and chi are observed, and padding
those two future lanes leaves both events unchanged. -/
theorem semRoundBad_pad_early {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F)
    (s₁ s₂ : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K) (c : K) (hi : i.val < 2) :
    semRoundBad (padC2Trace t) pub B (fun pre => virtualPoly pub B (padC2Trace t) pre)
        s₁ i pref c ↔
      semRoundBad t pub B (fun pre => virtualPoly pub B t pre) s₂ i pref c := by
  by_cases h0 : i.val = 0
  · simp only [semRoundBad, dif_pos h0, lambdaRoundBad_pad]
  · have h1 : i.val = 1 := by omega
    simp only [semRoundBad, dif_neg h0, dif_pos h1, chiRoundBad_pad]

#print axioms semRoundBad_pad_early

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- The guard is justified precisely in the parsed alpha phase. -/
theorem prefix_degreeOK (rs : List (Msg K K (SemMsg K) × Chal K K))
    (polys : Fin 10 → K[X]) (hlen : rs.length = 24)
    (hpolys : semPolys rs = some polys) (hdegree : ∀ j, (polys j).natDegree ≤ 27)
    (i : Fin 24) (sm : SemMsg K) (hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm) :
    14 ≤ (rs.take i.val).length → degreeOK sm := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  intro hi
  rw [htake] at hi
  cases sm with
  | none => trivial
  | h1 h g => trivial
  | roundPoly p =>
      have hp := polysOf_prefix rs polys i hi hlen hpolys (.roundPoly p) hcurrent
      have hidx : 14 + (i.val - 14) = i.val := by omega
      simp only [polysOf, htake, hidx, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte] at hp
      change p.natDegree ≤ 27
      rw [hp]
      exact hdegree _

#print axioms prefix_degreeOK

end
end R0P.SemD3Glue

namespace R0P.SemD3Glue
open R0P R0P.SemSource R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda LambdaRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem ofFn_prefix_getD (r : Fin 24 → K) (i : Fin 24) :
    (fun j : Fin i.val => ((List.ofFn r).take i.val).getD j.val 0) = semPrefix r i := by
  funext j
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
    List.getElem?_ofFn, dif_pos (by omega)]
  rfl

#print axioms ofFn_prefix_getD

/-- The current prefix contains the candidate appropriate to its C2 phase. -/
theorem candidate_mem_after_c2 {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (rs : List (Msg K K (SemMsg K) × Chal K K))
    (hlen : rs.length = 24) (hw gw : InitialWord K) (hc2 : c2Of rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (i : Fin 24) (hi : 2 ≤ i.val) (sm : SemMsg K)
    (hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm) :
    t ∈ candidates x (rs.take i.val) sm := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  by_cases hi2 : i.val = 2
  · have hm := c2Of_getElem rs hw gw (by omega) hc2
    have hcurrent' : (rs[2]'(by omega)).1 = .semantic sm := by simpa only [hi2] using hcurrent
    rw [hcurrent'] at hm
    have hsm : sm = .h1 hw gw := Msg.semantic.inj hm
    unfold candidates
    rw [htake, if_neg (by omega), if_pos hi2, hsm]
    exact ht
  · have hc2' : c2Of (rs.take i.val) = some (hw,gw) := (c2Of_take rs i.val (by omega)).trans hc2
    simp only [candidates, htake, show ¬ i.val < 2 by omega, if_false, hi2, hc2']
    exact ht

#print axioms candidate_mem_after_c2

/-- Padding supplies the pre-C2 candidate without fixing C2 before lambda. -/
theorem candidate_mem_before_c2 {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (rs : List (Msg K K (SemMsg K) × Chal K K))
    (hlen : rs.length = 24) (hw gw : InitialWord K)
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (i : Fin 24) (hi : i.val < 2) (sm : SemMsg K) :
    padC2Trace t ∈ candidates x (rs.take i.val) sm := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  have hne : (26 : Fin 29) ≠ 27 := by
    intro h
    have hv := congrArg Fin.val h
    change 26 = 27 at hv
    omega
  have h26 : padC2Trace t 26 = 0 := by
    simp only [padC2Trace, Function.update_of_ne hne, Function.update_self]
  have h27 : padC2Trace t 27 = 0 := by simp only [padC2Trace, Function.update_self]
  simp only [candidates, htake, if_pos hi, Finset.mem_filter]
  exact ⟨mem_Lambda_pad x hw gw t ht, h26, h27⟩

#print axioms candidate_mem_before_c2

/-- A candidate event in the complete parsed semantic transcript is an event
of the literal prefix classifier, with the correct pre/post-C2 candidate. -/
theorem candidate_bad_to_prefix {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (B : PackBasis F) (x : TypedContext K Sfield)
    (rs : List (Msg K K (SemMsg K) × Chal K K)) (hlen : rs.length = 24)
    (r : Fin 24 → K) (hparse : semChals rs = some (List.ofFn r))
    (hw gw : InitialWord K) (hc2 : c2Of rs = some (hw,gw))
    (polys : Fin 10 → K[X]) (hpolys : semPolys rs = some polys)
    (hdegree : ∀ j, (polys j).natDegree ≤ 27)
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw)) (i : Fin 24)
    (sm : SemMsg K) (hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm)
    (hbad : candidateRoundBad x.pub B t polys r i) :
    semanticBad B ⟨x, rs.take i.val⟩ sm (r i) := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  have hpre := ofFn_prefix_getD r i
  have hfinish (u : Trace K) (hu : u ∈ candidates x (rs.take i.val) sm)
      (hb : semRoundBad u x.pub B (fun pre => virtualPoly x.pub B u pre)
        (fixedStrat (polysOf (rs.take i.val) sm)) i (semPrefix r i) (r i)) :
      semanticBad B ⟨x, rs.take i.val⟩ sm (r i) := by
    refine ⟨by simpa only [htake] using i.isLt, (List.ofFn r).take i.val,
      semChals_take rs (List.ofFn r) hparse i.val,
      prefix_degreeOK rs polys hlen hpolys hdegree i sm hcurrent, u, hu, ?_⟩
    have lift (n : Nat) (hn : n < 24) (he : n = i.val) :
        semRoundBad u x.pub B (fun pre => virtualPoly x.pub B u pre)
          (fixedStrat (polysOf (rs.take i.val) sm)) ⟨n, hn⟩
          (fun j : Fin n => ((List.ofFn r).take i.val).getD j.val 0) (r i) := by
      subst n
      simpa only [hpre] using hb
    exact lift _ _ htake
  by_cases hi : i.val < 2
  · apply hfinish (padC2Trace t) (candidate_mem_before_c2 x rs hlen hw gw t ht i hi sm)
    exact (semRoundBad_pad_early t x.pub B _ _ i (semPrefix r i) (r i) hi).mpr hbad
  · apply hfinish t (candidate_mem_after_c2 x rs hlen hw gw hc2 t ht i (by omega) sm hcurrent)
    by_cases ha : 14 ≤ i.val
    · apply (semRoundBad_strat_congr t x.pub B (fun pre => virtualPoly x.pub B t pre)
        _ _ i (semPrefix r i) (r i) ha ?_).mpr hbad
      exact polysOf_prefix rs polys i ha hlen hpolys sm hcurrent
    · exact (semRoundBad_strat_early t x.pub B (fun pre => virtualPoly x.pub B t pre)
        _ _ i (semPrefix r i) (r i) (by omega)).mpr hbad

#print axioms candidate_bad_to_prefix

/-- No hit in the containing transcript excludes every candidate round event. -/
theorem no_hit_candidate_rounds {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (fallback1 : AspisR0.ChordGeometry.Point K) (B : PackBasis F) (x : TypedContext K Sfield)
    (rs tail : List (Msg K K (SemMsg K) × Chal K K)) (hlen : rs.length = 24)
    (r : Fin 24 → K) (hparse : semChals rs = some (List.ofFn r))
    (hw gw : InitialWord K) (hc2 : c2Of rs = some (hw,gw))
    (polys : Fin 10 → K[X]) (hpolys : semPolys rs = some polys)
    (hdegree : ∀ j, (polys j).natDegree ≤ 27)
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (hno : ¬ hitFrom (sourceDataWithFallback fallback1 B) x [] (rs ++ tail)) :
    ∀ i : Fin 24, ¬ candidateRoundBad x.pub B t polys r i := by
  intro i hbad
  obtain ⟨sm, hslot⟩ := semChals_getElem rs (List.ofFn r) hparse ⟨i.val, by omega⟩
  have hslot' : (rs[i.val]'(by omega)) = (.semantic sm, .semantic (r i)) := by
    simpa only [List.getElem_ofFn] using hslot
  have hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm := congrArg Prod.fst hslot'
  have hb := candidate_bad_to_prefix B x rs hlen r hparse hw gw hc2 polys hpolys hdegree
    t ht i sm hcurrent hbad
  apply hno
  apply roundBad_hitFrom (sourceDataWithFallback fallback1 B) x (rs ++ tail) [] i.val (by simp only [List.length_append]; omega)
  have htake : (rs ++ tail).take i.val = rs.take i.val :=
    List.take_append_of_le_length (by omega)
  have hget : ((rs ++ tail)[i.val]'(by simp only [List.length_append]; omega)) = rs[i.val]'(by omega) :=
    List.getElem_append_left (by omega)
  rw [List.nil_append, htake, hget, hslot']
  apply Or.inl
  refine ⟨sm, r i, ?_, rfl, rfl, hb⟩
  change (rs.take i.val).length < 24
  simp only [List.length_take, hlen]
  omega

#print axioms no_hit_candidate_rounds
end
end R0P.SemD3Glue

namespace R0P.SemD3Glue
open R0P R0P.SemSource R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses AspisR0.Chord AspisR0.ChordGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda LambdaRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- A fixed lane-zero basis, transported to the equal field stored in the
context; its two packing scalars are unchanged. -/
def contextBasis {Sfield : Fin 29 → Subfield K} (x : TypedContext K Sfield)
    (B : PackBasis (Sfield 0)) : PackBasis x.F where
  i := B.i
  u := B.u
  indep := by
    intro a b c d ha hb hc hd he
    apply B.indep a b c d
    · rw [x.lanesF 0 (by omega)]; exact ha
    · rw [x.lanesF 0 (by omega)]; exact hb
    · rw [x.lanesF 0 (by omega)]; exact hc
    · rw [x.lanesF 0 (by omega)]; exact hd
    · exact he

#print axioms contextBasis

/-- Sampler-free opening consequence: acceptance, the q22 guard, the actual
nonzero first challenge, and absence of an opening hit supply a witness. -/
theorem opening_decision_witness {Sfield : Fin 29 → Subfield K}
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (om : R0FS.Msg K) (hdec : R0FS.decision Q om = true)
    (hcard : SemSource.cardOK Q = true) (hno : ¬ R0FS.good Q.statement Q.rounds)
    (hfirst : ∀ (y : Fin 29 → Fin 2 → K) (γ : K),
      Q.rounds.head? = some (.values y, .field γ) → γ ≠ 0) :
    ∃ t : Trace K, R0FS.Witness Q.statement t := by
  obtain ⟨y, γ, v, κ, τ, q, α, f, s, hrs, _hm, hacc⟩ := R0FS.decision_true Q om hdec
  have hγ : γ ≠ 0 := hfirst y γ (by rw [hrs]; rfl)
  have hs : s.card = 22 := by
    simp only [SemSource.cardOK, hrs] at hcard
    simpa using hcard
  by_contra hw
  have hnd := R0FS.accept_not_doomed Q.statement y γ v κ τ α q f s
    (fun _ : Unit => (none : Option Unit)) hγ hs hacc
  apply hnd
  exact ⟨hw, by simpa only [hrs] using hno⟩

#print axioms opening_decision_witness

/-- The complete parsed-prefix bridge. The only semantic assumptions are the
three named G14 obligations. The first opening challenge premise is discharged
from the concrete round-26 sampler in `d3`, below. -/
theorem accepted_no_hit_extracted (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31-1) {Sfield : Fin 29 → Subfield K}
    (fallback1 : Point K) (B : PackBasis (Sfield 0))
    (hrows : ∀ (x : TypedContext K Sfield) (t : Trace K), HonestRows x.pub B t)
    (hdeg : ∀ (x : TypedContext K Sfield) (t : Trace K), VirtualDeg x.pub B t)
    (hchk : ∀ (x : TypedContext K Sfield) (t : Trace K), ChecksAccept x.pub B t)
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) (m : Msg K K (SemMsg K))
    (hdec : SemSource.decision B P m = true)
    (hno : ¬ hitFrom (sourceDataWithFallback fallback1 B) P.statement [] P.rounds)
    (hfirst : ∀ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)),
      openingView P = some Q → ∀ (y : Fin 29 → Fin 2 → K) (γ : K),
        Q.rounds.head? = some (.values y, .field γ) → γ ≠ 0) :
    ∃ t : Trace K, InputNoteExtracted P.statement.pub t := by
  unfold SemSource.decision at hdec
  obtain ⟨Q, cs, hcs, polys, om, hview, hparse, hpolys, hsum, _hm, hodec, hcard⟩ :=
    of_decide_eq_true hdec
  have hnogood : ¬ R0FS.good Q.statement Q.rounds := by
    intro hg
    exact hno (opening_good_hitFrom (sourceDataWithFallback fallback1 B) rfl rfl P Q hview hg)
  obtain ⟨mcoeff, hmcoeff⟩ := opening_decision_witness Q om hodec hcard hnogood (hfirst Q hview)
  let t := rowsOf P.statement.transport mcoeff
  have ht : R0FS.Witness Q.statement (coeffsOf P.statement.transport t) := by
    simpa only [t, coeffsOf_rowsOf] using hmcoeff
  obtain ⟨sem, cs', hw, gw, y, y₀, z₀, z₁, hcs', hb, hne, h₀, h₁, os,
    hsem, hparse', hc2, hrounds, hQ⟩ := openingView_some_structure P Q hview
  have htake : P.rounds.take 24 = sem := by
    rw [hrounds, ← hsem]
    exact List.take_left
  rw [htake] at hparse hpolys
  have heq : cs' = cs := Option.some.inj (hparse'.symm.trans hparse)
  subst cs'
  subst Q
  let r : Fin 24 → K := fun i => cs[i.val]'(by omega)
  have hrList : List.ofFn r = cs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hcs]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hα : (fun j : Fin 10 => cs[14 + j.val]'(by omega)) = semSlice r 14 10 := by
    funext j
    simp only [semSlice, semPrefixVal, dif_pos (show 14 + j.val < 24 by omega)]
    rfl
  have hy : y = honestClaims t (semSlice r 14 10) := by
    funext j l
    have h := ht.2.1 j l
    change y j l = AspisR0.RoundNormalization.dot
      (AspisR0.Opening.coeffWeight P.statement.transport
        (AspisR0.Opening.eqWeight (openingPoints (fun j => cs[14 + j.val]'(by omega)) j)))
      (coeffsOf P.statement.transport t l) at h
    rw [dot_coeffWeight_coeffsOf] at h
    simpa only [honestClaims, hα, AspisR0.RoundNormalization.dot, AspisR0.LinearDual.dot] using h
  have hsum' : sumcheckChecks P.statement.pub B (List.ofFn r) List.length_ofFn polys
      (honestClaims t (semSlice r 14 10)) := by
    simpa only [openingStmt, hrList, hy] using hsum
  have hparsenorm : semChals sem = some (List.ofFn r) := by rw [hrList]; exact hparse
  have hdegree : ∀ j, (polys j).natDegree ≤ 27 := hsum.1
  have hgood : ∀ i : Fin 24, ¬ candidateRoundBad P.statement.pub B t polys r i := by
    apply no_hit_candidate_rounds fallback1 B P.statement sem _ hsem r hparsenorm hw gw hc2
      polys hpolys hdegree t ((mem_LambdaRows _ _ _).mpr ht.1)
    simpa only [hrounds] using hno
  have hA := witness_baseTyped P.statement _ t ht
  have hprod := d3_core prime hprime P.statement (contextBasis P.statement B) t hA
    (hrows P.statement t) (hdeg P.statement t) (hchk P.statement t) r polys hsum' hgood
  exact ⟨t, semantic_extraction P.statement.pub t (r 0) (r 1) hprod
    (extraction_step P.statement.pub (r 0) (r 1) t)⟩

#print axioms accepted_no_hit_extracted
end
end R0P.SemD3Glue

namespace R0P.SemD3Glue
open FS FS2 FS2.Duplex R0P R0P.SemSource R0C.SemStatement
open AspisWideTower AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The mixed 31-round protocol, retaining its full duplex state and the
literal q22 final chain. Decoder construction is separate from D3. -/
def combinedProtocol {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (msg : Pf → Nat → Msg SemE SemE (SemMsg SemE))
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
        (Duplex.Chal (Chal SemE SemE)) × Msg SemE SemE (SemMsg SemE) ×
          Duplex.Chal (Chal SemE SemE)))) :
    FS2.Protocol (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
      (Duplex.Chal (Chal SemE SemE)) (Trace SemE) Pf (Addr L) State where
  r := 31
  msg := msg
  samp := combinedSampler p
  decode := decode
  extract := R0C.SemStatement.extract (sourceData B)

#print axioms combinedProtocol

/-- The source decision observes messages and challenge values, not retained
sampler states. -/
def combinedDecision {Sfield : Fin 29 → Subfield SemE}
    (B : PackBasis (Sfield 0))
    (P : FS.Prefix (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
      (Duplex.Chal (Chal SemE SemE))) (m : Msg SemE SemE (SemMsg SemE)) : Bool :=
  SemSource.decision B (valuePrefix P) m

#print axioms combinedDecision

/-- The first opening round occupies global round 26, without enumerating
any semantic prefix or opening list. -/
theorem opening_head_at_26 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingView P = some Q) :
    P.rounds[26]? = Q.rounds.head?.map (fun q => (Msg.opening q.1, Chal.opening q.2)) := by
  obtain ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hcs, hb, hne, h₀, h₁, os,
    hsem, hparse, hc2, hrounds, hQ⟩ := openingView_some_structure P Q hview
  subst Q
  rw [hrounds, List.getElem?_append_right (by omega), hsem]
  rw [show 26 - 24 = 2 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
    ← List.head?_eq_getElem?]
  simp only [openingPairs, List.head?_map]

#print axioms opening_head_at_26

/-- Lookup of an actual transcript uses the generic range theorem; no
concrete range or transcript is reduced. -/
theorem transcript_value_getElem {X M C S W Pf I A : Type} [DecidableEq I] [Inhabited A]
    (pr : FS2.Protocol X M (C × S) W Pf I A) (H : I → A) (x : X) (π : Pf)
    (n j : Nat) (hj : j < n) :
    (valuePrefix (pr.transcript H x π n)).rounds[j]? = some (pr.msg π j, (pr.chal H x π j).1) := by
  change (((pr.transcript H x π n).rounds).map (fun q => (q.1, q.2.1)))[j]? = _
  rw [R0C.V3.DQ.transcript_rounds_gen, List.map_map]
  rw [List.getElem?_eq_getElem (by simp only [List.length_map, List.length_range]; exact hj)]
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]

#print axioms transcript_value_getElem

/-- The value output by the literal one-block duplex sampler. -/
theorem oneBlock_value {X M C : Type} {L : Nat} (p : Duplex.Params M C L)
    (H : Addr L → State) (i : Nat) (P : FS.Prefix X M (Duplex.Chal C)) (m : M) :
    (eval H (Duplex.samp p i P m).toProgram).2.1 =
      p.σ i (H (squeezeA p (H (absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m))))) := by
  simp only [Duplex.samp, Sampler.toProgram, eval, multiProg, Function.update_self,
    Function.update_of_ne (Ne.symm (squeezeA_ne_advanceA p _))]

#print axioms oneBlock_value

/-- Nonzero gamma comes from the prescribed round-26 decoder and the actual
sampler evaluation, not an additional semantic premise. -/
theorem combined_chal26 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (msg : Pf → Nat → Msg SemE SemE (SemMsg SemE))
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
        (Duplex.Chal (Chal SemE SemE)) × Msg SemE SemE (SemMsg SemE) ×
          Duplex.Chal (Chal SemE SemE))))
    (hσ26 : ∀ s, p.σ 26 s = .opening (R0C.V3.DQ.σQ 0 s))
    (H : Addr L → State) (x : TypedContext SemE Sfield) (π : Pf) :
    ∃ a : State, ((combinedProtocol B p msg decode).chal H x π 26).1 =
      .opening (.field (R0C.ModuloField.gamma a)) := by
  let P26 := (combinedProtocol B p msg decode).transcript H x π 26
  let a : State := H (squeezeA p (H (absorbA p (stateOf p P26)
    (p.lbl 26) (p.enc (msg π 26)) (p.encLen (msg π 26)))))
  refine ⟨a, ?_⟩
  change (eval H (combinedSampler p 26 P26 (msg π 26)).toProgram).2.1 =
    .opening (.field (R0C.ModuloField.gamma a))
  rw [combinedSampler, if_pos (show 26 < 30 by omega), oneBlock_value]
  change p.σ 26 a = .opening (.field (R0C.ModuloField.gamma a))
  simpa only [R0C.V3.DQ.σQ] using hσ26 a

#print axioms combined_chal26

/-- D3 for the mixed protocol, with the three G14 bridges discharged.
The decoder identity specifies the existing gamma sampler. -/
theorem d3 (prime : Nat) [CharP SemE prime] (hprime : prime = 2^31-1)
    {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (msg : Pf → Nat → Msg SemE SemE (SemMsg SemE))
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext SemE Sfield) (Msg SemE SemE (SemMsg SemE))
        (Duplex.Chal (Chal SemE SemE)) × Msg SemE SemE (SemMsg SemE) ×
          Duplex.Chal (Chal SemE SemE))))
    (budget : Nat → ℚ)
    (hσ26 : ∀ s, p.σ 26 s = .opening (R0C.V3.DQ.σQ 0 s)) :
    FS2.D3 (combinedProtocol B p msg decode) (duplexRows B budget)
      (FS2.verifier (combinedProtocol B p msg decode) (combinedDecision B)) := by
  intro H x π T hd
  rw [FS2.verifier_eval]
  by_contra hfalse
  have hdec : combinedDecision B
      ((combinedProtocol B p msg decode).transcript H x π 31) (msg π 31) = true := by
    exact R0C.V3.DQ.bool_true_of_ne_false hfalse
  let P := valuePrefix ((combinedProtocol B p msg decode).transcript H x π 31)
  have hd' : (¬ ∃ t, InputNoteExtracted P.statement.pub t) ∧
      ¬ hitFrom (sourceData B) P.statement [] P.rounds := hd
  obtain ⟨t, ht⟩ := accepted_no_hit_extracted prime hprime circleFallback1 B
    (fun x t => honestRows x.pub B t) (fun x t => virtualDeg x.pub B t)
    (fun x t => checksAccept x.pub B t) P
    (msg π 31) hdec hd'.2 (by
      intro Q hview y γ hhead
      have hparsed := opening_head_at_26 P Q hview
      simp only [hhead, Option.map_some] at hparsed
      have hactual := transcript_value_getElem (combinedProtocol B p msg decode) H x π 31 26 (by omega)
      have hc := congrArg Prod.snd (Option.some.inj (hparsed.symm.trans hactual))
      obtain ⟨a, ha⟩ := combined_chal26 B p msg decode hσ26 H x π
      rw [ha] at hc
      have hγ : γ = R0C.ModuloField.gamma a := R0FS.Chal.field.inj (Chal.opening.inj hc)
      rw [hγ]
      exact R0C.ModuloField.gamma_ne_zero a)
  exact hd'.1 ⟨t, ht⟩

#print axioms d3
end
end R0P.SemD3Glue

namespace R0P.SemD3Glue
open FS FS2 FS2.Duplex R0P.SemSource R0C.SemStatement
open AspisWideTower AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
noncomputable section

/-- `chainS` reads only squeeze/advance addresses; changing the saved initial
state in otherwise identical opening parameters cannot change that chain. -/
theorem opening_chain_iv {C : Type} {L : Nat}
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (s₀ s₁ : State) (out : List State → List State → C) :
    ∀ (n : Nat) (s : State) (bs xs : List State),
      R0C.V3.DQ.chainS (openingParams p s₀) out n s bs xs =
        R0C.V3.DQ.chainS (openingParams p s₁) out n s bs xs := by
  intro n
  induction n with
  | zero => intro s bs xs; rfl
  | succ n ih =>
      intro s bs xs
      simp only [R0C.V3.DQ.chainS]
      congr 1
      funext b
      congr 1
      funext x
      exact ih x (bs ++ [b]) (xs ++ [x])

#print axioms opening_chain_iv

/-- Changing only `chainS`'s returned value preserves its entire oracle trace. -/
theorem chainS_eval_output_map {C D : Type} {L : Nat}
    (p : Duplex.Params (R0FS.Msg SemE) (R0FS.Chal SemE) L)
    (H : Addr L → State) (out : List State → List State → C) (f : C → D) :
    ∀ (n : Nat) (s : State) (bs xs : List State),
      eval H (R0C.V3.DQ.chainS p (fun bs xs => f (out bs xs)) n s bs xs).toProgram =
        let v := eval H (R0C.V3.DQ.chainS p out n s bs xs).toProgram
        (v.1, f v.2) := by
  intro n
  induction n with
  | zero => intro s bs xs; rfl
  | succ n ih =>
      intro s bs xs
      simp only [R0C.V3.DQ.chainS, Sampler.toProgram, eval]
      rw [ih]

#print axioms chainS_eval_output_map

/-- At the final opening message, the mixed sampler and the existing q22
sampler have identical read traces and outputs, apart from the outer opening
tag. The q22 instance starts at the actual full-prefix duplex state. -/
theorem combined_round30_sampQ {X : Type} {Sfield : Fin 29 → Subfield SemE} {L : Nat}
    (p : Duplex.Params (Msg SemE SemE (SemMsg SemE)) (Chal SemE SemE) L)
    (H : Addr L → State)
    (P : FS.Prefix X (Msg SemE SemE (SemMsg SemE)) (Duplex.Chal (Chal SemE SemE)))
    (stmt : R0FS.Stmt SemE Sfield) (om : R0FS.Msg SemE) :
    eval H (combinedSampler p 30 P (.opening om)).toProgram =
      let v := eval H (R0C.V3.DQ.sampQ (openingParams p (stateOf p P)) 4 ⟨stmt, []⟩ om).toProgram
      (v.1, openingChallenge v.2) := by
  let s := stateOf p P
  let a := absorbA p s (p.lbl 30) (p.enc (.opening om)) (p.encLen (.opening om))
  let s' := H a
  rw [combinedSampler, if_neg (show ¬ (30 : Nat) < 30 by omega), R0C.V3.DQ.sampQ,
    if_neg (show ¬ (4 : Nat) < 4 by omega)]
  change ((a, s') :: (eval H (R0C.V3.DQ.chainS (openingParams p s')
        (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []).toProgram).1,
      (eval H (R0C.V3.DQ.chainS (openingParams p s')
        (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []).toProgram).2) =
    ((a, s') :: (eval H (R0C.V3.DQ.chainS (openingParams p s)
        (R0C.V3.DQ.out4 s') 8 s' [] []).toProgram).1,
      openingChallenge (eval H (R0C.V3.DQ.chainS (openingParams p s)
        (R0C.V3.DQ.out4 s') 8 s' [] []).toProgram).2)
  rw [opening_chain_iv p s' s, chainS_eval_output_map]

#print axioms combined_round30_sampQ
end
end R0P.SemD3Glue
