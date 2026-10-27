import R1LiteralTypedWords
import R1CandidateBaseProjection
import R1ConcreteSpendExtraction

/-! Concrete M31 checking for a candidate selected from literal typed C1/C2
words. This is algebraic model plumbing only; it does not connect Rust
acceptance or byte extraction to the literal words. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisR1.LiteralSpendExtraction

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase

attribute [local irreducible] ConcreteBinding.candidates

abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed

theorem candidate_checked_witness
    (pub : Public M31Exact) (hshape : PublicOptionShape.canonical pub)
    (eK : QM31Exact →+* E)
    (c1 : LiteralTypedWords.C1Word) (c2 : LiteralTypedWords.C2Word)
    (t : ConcreteBinding.Tuple E)
    (ht : t ∈ ConcreteBinding.candidates (LiteralTypedWords.word embed eK c1 c2))
    (lam chi : E)
    (h : ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi
        (SemSource.rowsOf rowEquiv t) ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) (SemSource.rowsOf rowEquiv t)) :
    ∃ w : Wspend, checkM31 pub w = true := by
  let S := LiteralTypedWords.laneSubfield embed eK
  let W := LiteralTypedWords.word embed eK c1 c2
  have htyped : CandidateDescent.WordTyped S W :=
    LiteralTypedWords.word_typed embed eK c1 c2
  have hlanes : ∀ l : Fin 29, l.val < 26 →
      S l = embed.fieldRange := by
    intro l hl
    simp [S, LiteralTypedWords.laneSubfield,
      TypedRecoveredWords.laneSubfield, hl]
  have hbase := CandidateBaseProjection.rows_base_typed_of_uniform
    (E := E) S embed.fieldRange hlanes W htyped t ht rowEquiv
  obtain ⟨w, hw⟩ := ConcreteSpendExtraction.of_production pub
    (SemSource.rowsOf rowEquiv t) lam chi hshape hbase h
  exact ⟨w, (check_eq_true_iff pub w).mpr hw⟩

#print axioms candidate_checked_witness
end AspisR1.LiteralSpendExtraction
