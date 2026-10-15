import R1LiteralOpeningView
import R1LiteralOpeningStages
import R1SelectedOpeningEventMass

/-! Causal opening-event inputs. Prior words, semantic challenges and circle
points come only from the completed prefix; the current message supplies its
payload and, at the second fold, its literal folded word. The dummy challenge
is not read by the staged payload/word selectors. No terminal or source
correspondence is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningEvents

open AspisR1.LiteralTranscript
abbrev E := AspisWideTower.WideExact
abbrev Context := LiteralOpeningView.View
abbrev VWord := AspisPool.AlgorithmicCircleDecoderV7.FinalWord E

/-- A message-only extension for positional payload/word reads. -/
def withMessage (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :=
  P.rounds ++ [(m, (TranscriptView.Value.ordinary 0, 0))]

structure Gamma where
  context : Context
  payload : SelectedOpeningStages.Gamma

structure Kappa extends Gamma where
  payload28 : SelectedOpeningStages.Kappa
  gamma : E

structure First where
  context : Context
  payload : SelectedOpeningStages.First
  gamma : E
  kappa : E

structure Second where
  context : Context
  payload : SelectedOpeningStages.Second
  word : VWord
  gamma : E
  kappa : E
  alpha0 : E

def readGamma (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option Gamma := do
  let context ← LiteralOpeningView.read P.rounds
  let payload ← LiteralOpeningStages.readGamma (withMessage P m)
  pure ⟨context, payload⟩

def readKappa (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option Kappa := do
  let context ← LiteralOpeningView.read P.rounds
  let payload ← LiteralOpeningStages.readKappa (withMessage P m)
  let gamma ← LiteralChallengeRead.ordinaryAt P.rounds 27
  pure ⟨⟨context, payload.toGamma⟩, payload, gamma⟩

def readFirst (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option First := do
  let context ← LiteralOpeningView.read P.rounds
  let payload ← LiteralOpeningStages.readFirst (withMessage P m)
  let gamma ← LiteralChallengeRead.ordinaryAt P.rounds 27
  let kappa ← LiteralChallengeRead.ordinaryAt P.rounds 28
  pure ⟨context, payload, gamma, kappa⟩

def readSecond (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option Second := do
  let context ← LiteralOpeningView.read P.rounds
  let payload ← LiteralOpeningStages.readSecond (withMessage P m)
  let word ← LiteralTranscript.vAt (withMessage P m)
  let gamma ← LiteralChallengeRead.ordinaryAt P.rounds 27
  let kappa ← LiteralChallengeRead.ordinaryAt P.rounds 28
  let alpha0 ← LiteralChallengeRead.ordinaryAt P.rounds 29
  pure ⟨context, payload, word, gamma, kappa, alpha0⟩

def gammaBad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (x : E) : Prop :=
  match readGamma P m with
  | none => False
  | some v => x ∈ SelectedOpeningEvents.gammaBad v.context.word v.context.functionals v.payload

def kappaBad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (x : E) : Prop :=
  match readKappa P m with
  | none => False
  | some v => x ∈ SelectedOpeningEvents.kappaBad v.context.word v.context.functionals
      v.context.baseFunctional v.payload28 v.gamma

def firstBad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (x : E) : Prop :=
  match readFirst P m with
  | none => False
  | some v => x ∈ SelectedOpeningEvents.firstBad v.context.word v.context.functionals
      v.context.baseFunctional v.payload v.gamma v.kappa

def secondBad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (x : E) : Prop :=
  match readSecond P m with
  | none => False
  | some v => x ∈ SelectedOpeningEvents.secondBad v.context.word v.word v.context.functionals
      v.context.baseFunctional v.payload v.gamma v.kappa v.alpha0

end AspisR1.LiteralOpeningEvents
end
