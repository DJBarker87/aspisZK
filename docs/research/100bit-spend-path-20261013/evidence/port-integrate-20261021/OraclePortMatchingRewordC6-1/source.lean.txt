import OraclePortOpeningRewordC6
import OraclePortSemanticProjectionC6

/-! R13 reader transport replaces word annotations without requiring whole
literal-row equality. All transcript-derived scalar fields remain identical. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortMatchingRewordC6
open LiteralAcceptanceTerminal OraclePortReaderPlumbingC6 OraclePortSelectedArithmeticC4
attribute [local irreducible] LiteralTypedWords.word SelectedOpeningFunctionals.functionals
  SelectedOpeningFunctionals.rawBase

/-- The matching reader retains its exact scalar data while reading the new
word annotations. No unselected coordinate is equated with the old word. -/
theorem matching (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (d : MatchingSupport.Data E) (read : LiteralMatchingData.read rs = some d) :
    LiteralMatchingData.read (reword w rs) = some
      (withWords d (LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2)
        w.final) := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,
    hopen,hstage,h31,hword,hgamma,hkappa,h0,h1,hdata⟩ :=
    LiteralMatchingFacts.read_success_components rs d read
  obtain ⟨common',hopen',_,hF,hB,_,hW⟩ := OraclePortOpeningRewordC6.opening w rs common hopen
  have final := vAt w rs word hword
  unfold LiteralMatchingData.read
  simp only [hopen',readSecond,hstage,readAt,h31,final,ordinaryAt,hgamma,hkappa,h0,h1,
    Option.bind_eq_bind,Option.bind_some]
  rw [hW,hF,hB,hdata]
  rfl

/-- The semantic reader's complete scalar observation also transports. -/
theorem semantic (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (v v' : LiteralOpeningView.View)
    (left : LiteralOpeningView.read rs = some v)
    (right : LiteralOpeningView.read (reword w rs) = some v') :
    OraclePortSemanticProjectionC6.observe v'.semantic =
      OraclePortSemanticProjectionC6.observe v.semantic := by
  have l := (LiteralOpeningPrefixFacts.read_prefix_components rs v left).2.2.2.1
  have r := (LiteralOpeningPrefixFacts.read_prefix_components (reword w rs) v' right).2.2.2.1
  rw [reword_take] at r
  exact OraclePortSemanticProjectionC6.read_observe w 0 (rs.take 25) v.semantic v'.semantic l r

#print axioms matching
#print axioms semantic
end AspisR1.OraclePortMatchingRewordC6
end
