import FSV8V7FiniteTapeEmbedding
import AspisFormal.K1.V7Tag73OperationalOracleExposure
import AspisFormal.V5RankOneOpeningHiding

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7FiniteUniformBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSV8FreshTapeBudget FSV8FiniteTapePrefix
open FSV8V7FiniteTapeEmbedding
open AspisK1.V7Tag73TranscriptSchedule AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point

def finToFresh : ∀ {steps : Nat}, (Fin steps → Block) →
    FreshAnswerTape Block steps
  | 0, _ => PUnit.unit
  | n+1, f => (f 0, finToFresh (fun i => f i.succ))

def freshToFin : ∀ {steps : Nat}, FreshAnswerTape Block steps →
    (Fin steps → Block)
  | 0, _ => Fin.elim0
  | n+1, tape => Fin.cases tape.1 (fun i => freshToFin tape.2 i)

theorem freshToFin_finToFresh : ∀ {steps : Nat}
    (f : Fin steps → Block), freshToFin (finToFresh f) = f := by
  intro steps
  induction steps with
  | zero =>
      intro f
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro f
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih (fun k => f k.succ)) j

theorem finToFresh_freshToFin : ∀ {steps : Nat}
    (tape : FreshAnswerTape Block steps), finToFresh (freshToFin tape) = tape := by
  intro steps
  induction steps with
  | zero =>
      intro tape
      cases tape
      rfl
  | succ n ih =>
      intro tape
      rcases tape with ⟨head, tail⟩
      change (head, finToFresh (freshToFin tail)) = (head, tail)
      rw [ih]

theorem finToFresh_toList : ∀ (steps : Nat) (f : Fin steps → Block),
    freshAnswerTapeToList (finToFresh f) = List.ofFn f := by
  intro steps
  induction steps with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      rw [List.ofFn_succ]
      change f 0 :: freshAnswerTapeToList (finToFresh (fun i => f i.succ)) =
        f 0 :: List.ofFn (fun i => f i.succ)
      rw [ih]

def finFreshEquiv (steps : Nat) : (Fin steps → Block) ≃
    FreshAnswerTape Block steps where
  toFun := finToFresh
  invFun := freshToFin
  left_inv := freshToFin_finToFresh
  right_inv := finToFresh_freshToFin

theorem finFreshEquiv_list (steps : Nat) (f : Fin steps → Block) :
    freshAnswerTapeToList (finFreshEquiv steps f) =
      List.ofFn f := by
  change freshAnswerTapeToList (finToFresh f) = List.ofFn f
  exact finToFresh_toList steps f

theorem freshToFinEquiv_list (steps : Nat)
    (tape : FreshAnswerTape Block steps) :
    finFreshEquiv steps (freshToFin tape) = tape :=
  (finFreshEquiv steps).right_inv tape

theorem uniform_finFreshEquiv (steps : Nat) :
    (PMF.uniformOfFintype (Fin steps → Block)).map (finFreshEquiv steps) =
      PMF.uniformOfFintype (FreshAnswerTape Block steps) := by
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv (finFreshEquiv steps)

#print axioms finFreshEquiv_list
#print axioms uniform_finFreshEquiv
end AspisV8Completion.FSV8V7FiniteUniformBridge
