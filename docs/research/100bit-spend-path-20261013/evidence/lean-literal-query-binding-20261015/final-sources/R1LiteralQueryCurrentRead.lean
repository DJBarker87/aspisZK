import R1LiteralQueryRead

/-! A successfully decoded query challenge is visible at its current
round-31 prefix extension. This is positional list plumbing only. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryCurrentRead

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView

theorem queriesAt_current
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (xs : List Nat) (state : AspisV8R19.SourceDuplexStep.State) (q : Fin 22 → Fin 262144)
    (hround : P.round = 31)
    (hdecode : LiteralQueryRead.decode xs = some q) :
    LiteralQueryRead.queriesAt
      (P.ext m (Value.queries (.ok xs), state)).rounds 31 = some q := by
  have hlen : P.rounds.length = 31 := hround
  change LiteralQueryRead.queriesAt
    (P.rounds ++ [(m, (Value.queries (.ok xs), state))]) 31 = some q
  unfold LiteralQueryRead.queriesAt
  rw [List.getElem?_append_right (by omega : P.rounds.length ≤ 31)]
  rw [hlen, Nat.sub_self]
  simp [hdecode]

#print axioms queriesAt_current

end AspisR1.LiteralQueryCurrentRead
end
