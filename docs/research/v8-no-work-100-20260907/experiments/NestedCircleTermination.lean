import NestedCircleRunRefinement

/-! A decreasing source-read budget for the literal nested controller.
Forty-eight available squeeze blocks suffice for a terminal result. This
is not a uniformity, random-oracle freshness, or finite-measure theorem.
Unused source slots after a halt remain ghost padding, not source reads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.NestedCircleTermination
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisV8.NestedCircleRouting
open AspisV8.NestedCircleStatusRefinement
open AspisV8.NestedCircleRunRefinement

def Halted : State → Prop
  | .accepted _ _ => True
  | .aborted _ => True
  | _ => False

/-- Unread blocks in the currently running attempt, all remaining inner
attempts, and the later outer calls. Already pending blocks are subtracted
only once. The first sampler can precede nine second-phase ordinary calls. -/
def readBudget : State → Nat
  | .first inner pending => 4 * (3 - inner.val) + 36 - pending.length
  | .second _ outer inner pending =>
      4 * (3 - inner.val) + 12 * (2 - outer.val) - pending.length
  | _ => 0

theorem initial_budget : readBudget initial = 48 := rfl

theorem live_budget_positive (state : State) (ready : Ready state)
    (live : ¬Halted state) : 0 < readBudget state := by
  cases state with
  | first inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      have innerBound := inner.isLt
      simp only [readBudget]
      omega
  | second point outer inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      have innerBound := inner.isLt
      have outerBound := outer.isLt
      simp only [readBudget]
      omega
  | accepted first second => exact False.elim (live True.intro)
  | aborted reason => exact False.elim (live True.intro)

/-- Finishing an ordinary call either halts or skips at least the last
available block of that call before entering the next source attempt. -/
theorem ordinary_budget_decreases (circleMap : SecureCircleParameterMap)
    (state : State) (decoded : OrdinaryPrefixDecode)
    (ready : Ready state) (live : ¬Halted state) :
    readBudget (afterOrdinary circleMap state decoded) < readBudget state := by
  have positive := live_budget_positive state ready live
  cases state with
  | first inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      have innerBound := inner.isLt
      cases mapped : circleMap decoded.value with
      | none =>
          by_cases next : inner.val + 1 < 3
          · simp [afterOrdinary, mapped, next, readBudget]
            omega
          · simpa [afterOrdinary, mapped, next, readBudget] using positive
      | some point =>
          simp [afterOrdinary, mapped, readBudget]
          omega
  | second point outer inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have short := ordinary_needMore_short pending ready
      have innerBound := inner.isLt
      have outerBound := outer.isLt
      cases mapped : circleMap decoded.value with
      | none =>
          by_cases next : inner.val + 1 < 3
          · simp [afterOrdinary, mapped, next, readBudget]
            omega
          · simpa [afterOrdinary, mapped, next, readBudget] using positive
      | some nextPoint =>
          by_cases equal : nextPoint = point
          · by_cases next : outer.val + 1 < 3
            · simp [afterOrdinary, mapped, equal, next, readBudget]
              omega
            · simpa [afterOrdinary, mapped, equal, next, readBudget] using positive
          · simpa [afterOrdinary, mapped, equal, readBudget] using positive
  | accepted first second => exact False.elim (live True.intro)
  | aborted reason => exact False.elim (live True.intro)

/-- Each actual block read strictly decreases the live budget. Accepted
ordinary calls use the previous theorem; needMore consumes exactly one
pending-block position. No uniform distribution on the answer is assumed. -/
theorem answer_budget_decreases (circleMap : SecureCircleParameterMap)
    (state : State) (answer : Digest256) (ready : Ready state) (live : ¬Halted state) :
    readBudget (afterAnswer circleMap state answer) < readBudget state := by
  have positive := live_budget_positive state ready live
  cases state with
  | first inner pending =>
      cases status : ordinaryStatus (pending ++ [answer]) with
      | hardFailure => simpa [afterAnswer, status, readBudget] using positive
      | layoutFailure => exact False.elim (ordinary_no_layout _ status)
      | needMore =>
          have short := ordinary_needMore_short _ status
          simp only [List.length_append, List.length_singleton] at short
          simp only [readBudget] at positive
          simp [afterAnswer, status, short, readBudget]
          omega
      | accepted decoded =>
          simpa [afterAnswer, status] using
            ordinary_budget_decreases circleMap (.first inner pending) decoded ready live
  | second point outer inner pending =>
      cases status : ordinaryStatus (pending ++ [answer]) with
      | hardFailure => simpa [afterAnswer, status, readBudget] using positive
      | layoutFailure => exact False.elim (ordinary_no_layout _ status)
      | needMore =>
          have short := ordinary_needMore_short _ status
          simp only [List.length_append, List.length_singleton] at short
          simp only [readBudget] at positive
          simp [afterAnswer, status, short, readBudget]
          omega
      | accepted decoded =>
          simpa [afterAnswer, status] using
            ordinary_budget_decreases circleMap (.second point outer inner pending) decoded ready live
  | accepted first second => exact False.elim (live True.intro)
  | aborted reason => exact False.elim (live True.intro)

theorem halted_afterAnswer (circleMap : SecureCircleParameterMap)
    (state : State) (answer : Digest256) (halted : Halted state) :
    afterAnswer circleMap state answer = state := by
  cases state with
  | first inner pending => exact False.elim halted
  | second point outer inner pending => exact False.elim halted
  | accepted first second => rfl
  | aborted reason => rfl

/-- Subsequent mathematical fold positions after halt are ghost padding. -/
theorem halted_run (circleMap : SecureCircleParameterMap)
    (state : State) (tape : List Digest256) (halted : Halted state) :
    run circleMap state tape = state := by
  induction tape with
  | nil => rfl
  | cons answer unread ih =>
      simpa [NestedCircleRunRefinement.run, halted_afterAnswer circleMap state answer halted] using ih

theorem run_halts_of_budget (circleMap : SecureCircleParameterMap)
    (state : State) (tape : List Digest256) (ready : Ready state)
    (enough : readBudget state ≤ tape.length) : Halted (run circleMap state tape) := by
  induction tape generalizing state with
  | nil =>
      by_cases halted : Halted state
      · simpa [NestedCircleRunRefinement.run] using halted
      · have positive := live_budget_positive state ready halted
        simp only [List.length_nil] at enough
        omega
  | cons answer unread ih =>
      by_cases halted : Halted state
      · simpa [halted_run circleMap state (answer :: unread) halted] using halted
      · have decrease := answer_budget_decreases circleMap state answer ready halted
        have enoughTail : readBudget (afterAnswer circleMap state answer) ≤ unread.length := by
          simp only [List.length_cons] at enough
          omega
        have terminal := ih (afterAnswer circleMap state answer)
          (afterAnswer_ready circleMap state answer) enoughTail
        simpa [NestedCircleRunRefinement.run] using terminal

/-- Actual three first-circle attempts plus three-by-three second attempts
need at most 48 squeeze-output blocks. Advance-domain oracle calls are not
counted as these blocks, and unused retries are not actual source reads. -/
theorem forty_eight_blocks_halt (circleMap : SecureCircleParameterMap)
    (tape : List Digest256) (enough : 48 ≤ tape.length) :
    Halted (run circleMap initial tape) := by
  apply run_halts_of_budget circleMap initial tape
  · rfl
  · simpa only [initial_budget] using enough

/-- Adequate finite input eliminates the waiting outcome, so literal source
None is now EXACTLY a controller abort. No error reason is synthesized from
short-input failure; short tapes do not satisfy this theorem's guard. -/
theorem source_none_iff_abort (circleMap : SecureCircleParameterMap)
    (tape : List Digest256) (enough : 48 ≤ tape.length) :
    sourcePair circleMap tape = none ↔
      ∃ reason, run circleMap initial tape = .aborted reason := by
  have terminal := forty_eight_blocks_halt circleMap tape enough
  rw [source_pair_refines]
  cases result : run circleMap initial tape <;>
    simp_all [Halted, acceptedResult]

#print axioms initial_budget
#print axioms live_budget_positive
#print axioms ordinary_budget_decreases
#print axioms answer_budget_decreases
#print axioms halted_afterAnswer
#print axioms halted_run
#print axioms run_halts_of_budget
#print axioms forty_eight_blocks_halt
#print axioms source_none_iff_abort
end
end AspisV8.NestedCircleTermination
