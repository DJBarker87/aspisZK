import OraclePortReaderPlumbingC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortOpeningRewordC6
open LiteralAcceptanceTerminal OraclePortReaderPlumbingC6 OraclePortSemanticObservationsC6
attribute [local instance] Classical.propDecidable
attribute [local irreducible] LiteralTypedWords.word SelectedOpeningFunctionals.functionals
  SelectedOpeningFunctionals.rawBase R0P.SemSource.circleSampleParameter0 R0P.SemSource.circleSampleParameter1

/-- Successful common-reader reconstruction preserves its scalar context and
replaces only whole-word annotations and the semantic C2 callback. -/
theorem opening (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (v : LiteralOpeningView.View) (read : LiteralOpeningView.read rs = some v) :
    ∃ v', LiteralOpeningView.read (reword w rs) = some v' ∧
      scalarPairs v'.semantic = scalarPairs v.semantic ∧
      v'.functionals = v.functionals ∧ v'.baseFunctional = v.baseFunctional ∧
      v'.circlePoints = v.circlePoints ∧
      v'.word = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2 := by
  obtain ⟨c1,c2,sem,word⟩ := LiteralOpeningFunctionalFacts.read_semantic_components rs v read
  have length := (LiteralOpeningPrefixFacts.read_prefix_components rs v read).1
  obtain ⟨semantic,hsemantic,same⟩ := semantic_success w 0 (rs.take 25) v.semantic sem
  have cs : semantic.map Prod.snd = v.semantic.map Prod.snd := by
    have h := congrArg (List.map Prod.snd) same
    simpa only [scalarPairs,List.map_map,Function.comp_def] using h
  have first := c1At w rs v.c1 c1
  have second := c2At w rs v.c2 c2
  unfold LiteralOpeningView.read at read
  rw [dif_pos length,c1,c2] at read
  simp only [Option.bind_eq_bind,Option.bind_some] at read
  split at read
  · rename_i hn
    rw [sem] at hn
    cases hn
  · rename_i parsed hpsem
    have eq : parsed = v.semantic := Option.some.inj (hpsem.symm.trans sem)
    subst parsed
    cases hz0 : LiteralChallengeRead.ordinaryAt rs 25 with
    | none => simp only [hz0,Option.bind_none,reduceCtorEq] at read
    | some z0 =>
      cases hz1 : LiteralChallengeRead.ordinaryAt rs 26 with
      | none => simp only [hz0,hz1,Option.bind_none,Option.bind_some,reduceCtorEq] at read
      | some z1 =>
        simp only [hz0,hz1,Option.bind_eq_bind,Option.bind_some,Option.some.injEq] at read
        have readValue := Option.some.inj read
        have hf := congrArg LiteralOpeningView.View.functionals readValue
        have hb := congrArg LiteralOpeningView.View.baseFunctional readValue
        have hp := congrArg LiteralOpeningView.View.circlePoints readValue
        have length' : ((reword w rs).take 25).length = 25 := by
          rw [reword_take]
          simpa only [reword,List.length_map] using length
        unfold LiteralOpeningView.read
        rw [dif_pos length',first,second]
        simp only [Option.bind_eq_bind,Option.bind_some]
        split
        · rename_i hn
          rw [reword_take,hsemantic] at hn
          cases hn
        · rename_i parsed hpsem'
          have eq : parsed = semantic := by
            rw [reword_take,hsemantic] at hpsem'
            exact Option.some.inj hpsem'.symm
          subst parsed
          simp only [ordinaryAt,hz0,hz1,Option.bind_eq_bind,Option.bind_some]
          refine ⟨_,rfl,same,?_,?_,hp,rfl⟩
          · dsimp only at cs ⊢
            rw [cs]
            exact hf
          · dsimp only at cs ⊢
            rw [cs]
            exact hb

#print axioms opening
end AspisR1.OraclePortOpeningRewordC6
end
