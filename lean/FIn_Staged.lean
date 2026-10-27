import PAln_MatchingFacts
set_option autoImplicit false
namespace AspisR1.FIn_Staged

theorem reads (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (s : LiteralOpeningStages.Second) (run : LiteralOpeningStages.readSecond rs = some s) :
    LiteralOpeningStages.readAt rs 29 (OpeningRecordCodec.decode .first) = some s.toFirst.row29 ∧
    LiteralOpeningStages.readAt rs 30 (OpeningRecordCodec.decode .second) = some s.row30 := by
  unfold LiteralOpeningStages.readSecond at run
  cases hfirst : LiteralOpeningStages.readFirst rs with
  | none => simp only [hfirst,Option.bind_none] at run; cases run
  | some first =>
    cases h30 : LiteralOpeningStages.readAt rs 30 (OpeningRecordCodec.decode .second) with
    | none => simp only [hfirst,h30,Option.bind_some,Option.bind_none] at run; cases run
    | some second =>
      simp only [hfirst,h30,Option.bind_some,Option.pure_def] at run
      cases run
      refine ⟨?_,rfl⟩
      unfold LiteralOpeningStages.readFirst at hfirst
      cases hk : LiteralOpeningStages.readKappa rs with
      | none => simp only [hk,Option.bind_none] at hfirst; cases hfirst
      | some kappa =>
        cases h29 : LiteralOpeningStages.readAt rs 29 (OpeningRecordCodec.decode .first) with
        | none => simp only [hk,h29,Option.bind_some,Option.bind_none] at hfirst; cases hfirst
        | some row =>
          simp only [hk,h29,Option.bind_some,Option.pure_def] at hfirst
          cases hfirst
          rfl

#print axioms reads
end AspisR1.FIn_Staged
