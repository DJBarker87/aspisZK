import NestedCircleStatusRefinement

/-! Whole finite-tape accepted-result refinement through literal source
continuations. No measure, freshness, coordinate routing, or FS law occurs.
On short tapes source None may mean a waiting controller, not hard abort.
The separate 48-block termination bound is not assumed here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.NestedCircleRunRefinement
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisV8.DistinctCircleDecoder
open AspisV8.NestedCircleRouting
open AspisV8.NestedCircleStatusRefinement

abbrev PointPair := SecureCirclePointBytes × SecureCirclePointBytes

def secondSource (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (outer : Nat)
    (blocks : List Digest256) : Option PointPair := do
  let decoded ← decodeDistinctPrefix circleMap firstPoint outer blocks
  let point ← circleMap decoded.value
  pure (firstPoint, point)

def firstSource (circleMap : SecureCircleParameterMap) (inner : Nat)
    (blocks : List Digest256) : Option PointPair := do
  let decoded ← decodeSecureCirclePrefix circleMap inner blocks
  let point ← circleMap decoded.value
  secondSource circleMap point 3 decoded.remainingBlocks

/-- `outer` counts outer retries AFTER the currently running circle call. -/
def innerSource (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (outer inner : Nat)
    (blocks : List Digest256) : Option PointPair := do
  let decoded ← decodeSecureCirclePrefix circleMap inner blocks
  let point ← circleMap decoded.value
  if point = firstPoint then
    secondSource circleMap firstPoint outer decoded.remainingBlocks
  else pure (firstPoint, point)

/-- The literal first circle3 call, followed by distinct3(circle3) on the
ACTUAL returned suffix. Successful map matches are evaluated as source code,
not supplied as hypotheses. -/
def sourcePair (circleMap : SecureCircleParameterMap)
    (blocks : List Digest256) : Option PointPair := firstSource circleMap 3 blocks

def interpret (circleMap : SecureCircleParameterMap) (state : State)
    (unread : List Digest256) : Option PointPair :=
  match state with
  | .first inner pending => firstSource circleMap (3 - inner.val) (pending ++ unread)
  | .second point outer inner pending =>
      innerSource circleMap point (2 - outer.val) (3 - inner.val) (pending ++ unread)
  | .accepted firstPoint secondPoint => some (firstPoint, secondPoint)
  | .aborted _ => none

def Ready : State → Prop
  | .first _ pending => ordinaryStatus pending = .needMore
  | .second _ _ _ pending => ordinaryStatus pending = .needMore
  | _ => True

def acceptedResult : State → Option PointPair
  | .accepted firstPoint secondPoint => some (firstPoint, secondPoint)
  | _ => none

def initial : State := .first 0 []

def run (circleMap : SecureCircleParameterMap) (state : State)
    (tape : List Digest256) : State := tape.foldl (afterAnswer circleMap) state

theorem secondSource_succ (circleMap : SecureCircleParameterMap)
    (point : SecureCirclePointBytes) (outer : Nat) (blocks : List Digest256) :
    secondSource circleMap point (outer + 1) blocks =
      innerSource circleMap point outer 3 blocks := by
  simp only [secondSource, decodeDistinctPrefix, innerSource]
  cases decodedRun : decodeSecureCirclePrefix circleMap 3 blocks with
  | none => simp
  | some decoded =>
      cases mapped : circleMap decoded.value with
      | none => simp [mapped]
      | some next =>
          by_cases equal : next = point <;> simp [mapped, equal]

theorem firstSource_failure (circleMap : SecureCircleParameterMap)
    (attempts : Nat) (blocks : List Digest256)
    (failed : decodeOrdinaryPrefix blocks = none) :
    firstSource circleMap (attempts + 1) blocks = none := by
  simp [firstSource, decodeSecureCirclePrefix, failed]

theorem innerSource_failure (circleMap : SecureCircleParameterMap)
    (point : SecureCirclePointBytes) (outer attempts : Nat) (blocks : List Digest256)
    (failed : decodeOrdinaryPrefix blocks = none) :
    innerSource circleMap point outer (attempts + 1) blocks = none := by
  simp [innerSource, decodeSecureCirclePrefix, failed]

theorem firstSource_step (circleMap : SecureCircleParameterMap)
    (attempts : Nat) (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (source : decodeOrdinaryPrefix blocks = some decoded) :
    firstSource circleMap (attempts + 1) blocks =
      match circleMap decoded.value with
      | none => firstSource circleMap attempts decoded.remainingBlocks
      | some point => secondSource circleMap point 3 decoded.remainingBlocks := by
  cases mapped : circleMap decoded.value <;>
    simp [firstSource, decodeSecureCirclePrefix, source, mapped]

theorem innerSource_step (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (outer attempts : Nat)
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (source : decodeOrdinaryPrefix blocks = some decoded) :
    innerSource circleMap firstPoint outer (attempts + 1) blocks =
      match circleMap decoded.value with
      | none => innerSource circleMap firstPoint outer attempts decoded.remainingBlocks
      | some point => if point = firstPoint then
          secondSource circleMap firstPoint outer decoded.remainingBlocks
        else some (firstPoint, point) := by
  cases mapped : circleMap decoded.value <;>
    simp [innerSource, decodeSecureCirclePrefix, source, mapped]

/-- One successful ordinary source call advances the first phase on its
returned suffix, including exact exhausted-inner and successful-map cases. -/
theorem first_ordinary_step (circleMap : SecureCircleParameterMap)
    (inner : Fin 3) (pending unread : List Digest256) (decoded : OrdinaryPrefixDecode)
    (source : decodeOrdinaryPrefix (pending ++ unread) = some decoded) :
    interpret circleMap (.first inner pending) unread =
      interpret circleMap (afterOrdinary circleMap (.first inner pending) decoded)
        decoded.remainingBlocks := by
  have innerBound := inner.isLt
  have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
  change firstSource circleMap (3 - inner.val) (pending ++ unread) = _
  rw [count, firstSource_step circleMap (2 - inner.val) _ decoded source]
  cases mapped : circleMap decoded.value with
  | none =>
      by_cases next : inner.val + 1 < 3
      · have remaining : 3 - (inner.val + 1) = 2 - inner.val := by omega
        simp [afterOrdinary, mapped, next, interpret, remaining]
      · have exhausted : 2 - inner.val = 0 := by omega
        simp [afterOrdinary, mapped, next, interpret, exhausted,
          firstSource, decodeSecureCirclePrefix]
  | some point =>
      simpa [afterOrdinary, mapped, interpret] using
        secondSource_succ circleMap point 2 decoded.remainingBlocks

/-- The second phase preserves the current inner retry budget; only a
successful duplicate starts a fresh circle3 under a remaining outer retry. -/
theorem second_ordinary_step (circleMap : SecureCircleParameterMap)
    (point : SecureCirclePointBytes) (outer inner : Fin 3)
    (pending unread : List Digest256) (decoded : OrdinaryPrefixDecode)
    (source : decodeOrdinaryPrefix (pending ++ unread) = some decoded) :
    interpret circleMap (.second point outer inner pending) unread =
      interpret circleMap (afterOrdinary circleMap (.second point outer inner pending) decoded)
        decoded.remainingBlocks := by
  have innerBound := inner.isLt
  have outerBound := outer.isLt
  have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
  change innerSource circleMap point (2 - outer.val) (3 - inner.val) (pending ++ unread) = _
  rw [count, innerSource_step circleMap point (2 - outer.val) (2 - inner.val) _ decoded source]
  cases mapped : circleMap decoded.value with
  | none =>
      by_cases next : inner.val + 1 < 3
      · have remaining : 3 - (inner.val + 1) = 2 - inner.val := by omega
        simp [afterOrdinary, mapped, next, interpret, remaining]
      · have exhausted : 2 - inner.val = 0 := by omega
        simp [afterOrdinary, mapped, next, interpret, exhausted,
          innerSource, decodeSecureCirclePrefix]
  | some nextPoint =>
      by_cases equal : nextPoint = point
      · by_cases next : outer.val + 1 < 3
        · have remaining : 2 - outer.val = (2 - (outer.val + 1)) + 1 := by omega
          simpa [afterOrdinary, mapped, equal, next, interpret, remaining] using
            secondSource_succ circleMap point (2 - (outer.val + 1)) decoded.remainingBlocks
        · have exhausted : 2 - outer.val = 0 := by omega
          simp [afterOrdinary, mapped, equal, next, interpret, exhausted,
            secondSource, decodeDistinctPrefix]
      · simp [afterOrdinary, mapped, equal, interpret]

theorem afterOrdinary_remaining (circleMap : SecureCircleParameterMap)
    (state : State) (decoded : OrdinaryPrefixDecode) (tail : List Digest256) :
    afterOrdinary circleMap state {decoded with remainingBlocks := tail} =
      afterOrdinary circleMap state decoded := by
  cases state <;> rfl

theorem afterOrdinary_ready (circleMap : SecureCircleParameterMap)
    (state : State) (decoded : OrdinaryPrefixDecode) :
    Ready (afterOrdinary circleMap state decoded) := by
  cases state with
  | first inner pending =>
      cases mapped : circleMap decoded.value with
      | some point => simp [afterOrdinary, mapped, Ready, ordinaryStatus]
      | none =>
          by_cases next : inner.val + 1 < 3 <;>
            simp [afterOrdinary, mapped, next, Ready, ordinaryStatus]
  | second point outer inner pending =>
      cases mapped : circleMap decoded.value with
      | none =>
          by_cases next : inner.val + 1 < 3 <;>
            simp [afterOrdinary, mapped, next, Ready, ordinaryStatus]
      | some nextPoint =>
          by_cases equal : nextPoint = point
          · by_cases next : outer.val + 1 < 3 <;>
              simp [afterOrdinary, mapped, equal, next, Ready, ordinaryStatus]
          · simp [afterOrdinary, mapped, equal, Ready]
  | accepted first second => trivial
  | aborted reason => trivial

theorem afterAnswer_ready (circleMap : SecureCircleParameterMap)
    (state : State) (answer : Digest256) : Ready (afterAnswer circleMap state answer) := by
  cases state with
  | first inner pending =>
      cases status : ordinaryStatus (pending ++ [answer]) with
      | hardFailure => simp [afterAnswer, status, Ready]
      | layoutFailure => simp [afterAnswer, status, Ready]
      | needMore =>
          by_cases short : pending.length + 1 < 4 <;>
            simp [afterAnswer, status, short, Ready]
      | accepted decoded =>
          simpa [afterAnswer, status] using
            afterOrdinary_ready circleMap (.first inner pending) decoded
  | second point outer inner pending =>
      cases status : ordinaryStatus (pending ++ [answer]) with
      | hardFailure => simp [afterAnswer, status, Ready]
      | layoutFailure => simp [afterAnswer, status, Ready]
      | needMore =>
          by_cases short : pending.length + 1 < 4 <;>
            simp [afterAnswer, status, short, Ready]
      | accepted decoded =>
          simpa [afterAnswer, status] using
            afterOrdinary_ready circleMap (.second point outer inner pending) decoded
  | accepted first second => trivial
  | aborted reason => trivial

theorem hard_on_unread (pending : List Digest256) (answer : Digest256)
    (unread : List Digest256)
    (failed : ordinaryStatus (pending ++ [answer]) = .hardFailure) :
    decodeOrdinaryPrefix (pending ++ answer :: unread) = none := by
  have extended := ordinary_hard_failure_append (pending ++ [answer]) unread failed
  have projected := ordinaryStatus_forget ((pending ++ [answer]) ++ unread)
  rw [extended] at projected
  simpa [PrefixStatus.forget, List.append_assoc] using projected.symm

/-- Accepted data are reconstructed on precisely the appended unread tail.
No expected decoder output or whole-block remainder equality is supplied. -/
theorem accepted_on_unread (pending : List Digest256) (answer : Digest256)
    (unread : List Digest256) (decoded : OrdinaryPrefixDecode)
    (waiting : ordinaryStatus pending = .needMore)
    (accepted : ordinaryStatus (pending ++ [answer]) = .accepted decoded) :
    decodeOrdinaryPrefix (pending ++ answer :: unread) =
      some {decoded with remainingBlocks := unread} := by
  have source : decodeOrdinaryPrefix (pending ++ [answer]) = some decoded := by
    rw [← ordinaryStatus_forget, accepted]
    rfl
  have empty := (ordinary_next_accept_empty pending answer decoded waiting accepted).2
  have extended := decodeOrdinaryPrefix_append_of_some (pending ++ [answer]) unread decoded source
  simpa [appendOrdinaryRemaining, empty, List.append_assoc] using extended

/-- The controller names/uses one next block, then leaves the literal source
continuation on the exact remaining tape unchanged. -/
theorem one_block_preserves (circleMap : SecureCircleParameterMap)
    (state : State) (answer : Digest256) (unread : List Digest256)
    (ready : Ready state) :
    interpret circleMap state (answer :: unread) =
      interpret circleMap (afterAnswer circleMap state answer) unread := by
  cases state with
  | first inner pending =>
      change ordinaryStatus pending = .needMore at ready
      cases status : ordinaryStatus (pending ++ [answer]) with
      | layoutFailure => exact False.elim (ordinary_no_layout _ status)
      | hardFailure =>
          have failed := hard_on_unread pending answer unread status
          have bound := inner.isLt
          have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
          simp [interpret, count, firstSource_failure circleMap _ _ failed,
            afterAnswer, status]
      | needMore =>
          have short := ordinary_needMore_short _ status
          simp only [List.length_append, List.length_singleton] at short
          simp [afterAnswer, status, short, interpret, List.append_assoc]
      | accepted decoded =>
          have source := accepted_on_unread pending answer unread decoded ready status
          have step := first_ordinary_step circleMap inner pending (answer :: unread)
            {decoded with remainingBlocks := unread} source
          simpa [afterAnswer, status, afterOrdinary_remaining] using step
  | second point outer inner pending =>
      change ordinaryStatus pending = .needMore at ready
      cases status : ordinaryStatus (pending ++ [answer]) with
      | layoutFailure => exact False.elim (ordinary_no_layout _ status)
      | hardFailure =>
          have failed := hard_on_unread pending answer unread status
          have bound := inner.isLt
          have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
          simp [interpret, count, innerSource_failure circleMap point _ _ _ failed,
            afterAnswer, status]
      | needMore =>
          have short := ordinary_needMore_short _ status
          simp only [List.length_append, List.length_singleton] at short
          simp [afterAnswer, status, short, interpret, List.append_assoc]
      | accepted decoded =>
          have source := accepted_on_unread pending answer unread decoded ready status
          have step := second_ordinary_step circleMap point outer inner pending (answer :: unread)
            {decoded with remainingBlocks := unread} source
          simpa [afterAnswer, status, afterOrdinary_remaining] using step
  | accepted first second => rfl
  | aborted reason => rfl

theorem empty_interpret (circleMap : SecureCircleParameterMap) (state : State)
    (ready : Ready state) : interpret circleMap state [] = acceptedResult state := by
  cases state with
  | first inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have failed : decodeOrdinaryPrefix pending = none := by
        rw [← ordinaryStatus_forget, ready]
        rfl
      have bound := inner.isLt
      have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
      simp [interpret, acceptedResult, count, firstSource_failure circleMap _ _ failed]
  | second point outer inner pending =>
      change ordinaryStatus pending = .needMore at ready
      have failed : decodeOrdinaryPrefix pending = none := by
        rw [← ordinaryStatus_forget, ready]
        rfl
      have bound := inner.isLt
      have count : 3 - inner.val = (2 - inner.val) + 1 := by omega
      simp [interpret, acceptedResult, count, innerSource_failure circleMap point _ _ _ failed]
  | accepted first second => rfl
  | aborted reason => rfl

/-- The full chronological tape is traversed by the actual afterAnswer
controller. Halted updates are only ghost padding: their state is unchanged. -/
theorem run_refines (circleMap : SecureCircleParameterMap) (state : State)
    (tape : List Digest256) (ready : Ready state) :
    interpret circleMap state tape = acceptedResult (run circleMap state tape) := by
  induction tape generalizing state with
  | nil => simpa [run] using empty_interpret circleMap state ready
  | cons answer unread ih =>
      rw [one_block_preserves circleMap state answer unread ready]
      simpa [run] using ih (afterAnswer circleMap state answer)
        (afterAnswer_ready circleMap state answer)

/-- Literal first-circle3 then distinct3(circle3) accepted-result equality,
with no source-correspondence premise and no future-block choice. -/
theorem source_pair_refines (circleMap : SecureCircleParameterMap) (tape : List Digest256) :
    sourcePair circleMap tape = acceptedResult (run circleMap initial tape) := by
  have ready : Ready initial := rfl
  simpa [sourcePair, initial, interpret] using run_refines circleMap initial tape ready

theorem accepted_iff (circleMap : SecureCircleParameterMap) (tape : List Digest256)
    (firstPoint secondPoint : SecureCirclePointBytes) :
    sourcePair circleMap tape = some (firstPoint, secondPoint) ↔
      run circleMap initial tape = .accepted firstPoint secondPoint := by
  rw [source_pair_refines]
  cases result : run circleMap initial tape <;> simp [acceptedResult]

/-- Every actual controller abort gives literal source None. The converse
is intentionally not asserted for short input, which may leave Ready state. -/
theorem abort_implies_source_none (circleMap : SecureCircleParameterMap)
    (tape : List Digest256) (reason : AbortReason)
    (aborted : run circleMap initial tape = .aborted reason) :
    sourcePair circleMap tape = none := by
  rw [source_pair_refines, aborted]
  rfl

#print axioms secondSource_succ
#print axioms firstSource_failure
#print axioms innerSource_failure
#print axioms firstSource_step
#print axioms innerSource_step
#print axioms first_ordinary_step
#print axioms second_ordinary_step
#print axioms afterOrdinary_remaining
#print axioms afterOrdinary_ready
#print axioms afterAnswer_ready
#print axioms hard_on_unread
#print axioms accepted_on_unread
#print axioms one_block_preserves
#print axioms empty_interpret
#print axioms run_refines
#print axioms source_pair_refines
#print axioms accepted_iff
#print axioms abort_implies_source_none
end
end AspisV8.NestedCircleRunRefinement
