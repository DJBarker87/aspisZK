import OraclePortSelectedDraft
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_QueryInjective
open OraclePortSelectedDraft
/-- Injectivity is a consequence of the actual accepted sampler projection. -/
theorem value (tr : RawCutTranscriptRun.ErasedPrefix) (q : Fin 22 → Fin 262144)
    (read : queries tr=some q) : Function.Injective q := by
  unfold queries at read
  cases entry : tr.rounds[31]? with
  | none => simp only [entry,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    rcases c with ⟨v,state⟩
    cases v with
    | ordinary e => simp [entry] at read
    | queries result =>
      cases result with
      | error e => simp [entry] at read
      | ok xs =>
        have decoded : LiteralQueryRead.decode xs=some q := by simpa only [entry,Option.bind_eq_bind,Option.bind_some] using read
        exact (LiteralQueryRead.decode_success xs q decoded).2
#print axioms value
end AspisR1.FJo_QueryInjective
end
