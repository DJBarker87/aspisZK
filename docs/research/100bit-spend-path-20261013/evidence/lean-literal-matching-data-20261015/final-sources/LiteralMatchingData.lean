import R1LiteralOpeningEvents
import R1SelectedOpeningData

/-! Assemble matching-support data from fixed literal message/challenge entries.
The query-row view adds the current message, with a dummy challenge that no
reader consumes. The rho-row view uses completed entries only. These are
reader definitions, not acceptance, source-refinement or extraction theorems. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralMatchingData

abbrev E := AspisWideTower.WideExact

/-- Read completed payloads through row 31 and ordinary challenges through 30. -/
def read (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option (MatchingSupport.Data E) := do
  let common ← LiteralOpeningView.read rs
  let staged ← LiteralOpeningStages.readSecond rs
  let row31 ← LiteralOpeningStages.readAt rs 31 (OpeningRecordCodec.decode .final)
  let word ← LiteralTranscript.vAt rs
  let gamma ← LiteralChallengeRead.ordinaryAt rs 27
  let kappa ← LiteralChallengeRead.ordinaryAt rs 28
  let alpha0 ← LiteralChallengeRead.ordinaryAt rs 29
  let alpha1 ← LiteralChallengeRead.ordinaryAt rs 30
  let payloads : SelectedOpeningData.Payloads := {
    row25 := staged.toFirst.toKappa.toGamma.row25
    row26 := staged.toFirst.toKappa.toGamma.row26
    row27 := staged.toFirst.toKappa.toGamma.row27
    row28 := staged.toFirst.toKappa.row28
    row29 := staged.toFirst.row29
    row30 := staged.row30
    row31 := row31
  }
  pure (SelectedOpeningData.data payloads common.word word
    common.functionals common.baseFunctional gamma kappa alpha0 alpha1)

def atQuery (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :=
  read (LiteralOpeningEvents.withMessage P m)

def beforeRho (P : LiteralTranscript.Prefix) := read P.rounds

#print axioms read

end AspisR1.LiteralMatchingData
end
