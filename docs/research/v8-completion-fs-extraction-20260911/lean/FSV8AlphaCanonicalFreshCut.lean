import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters

/-!
# Canonical fresh cuts for V8 alpha labels

This source-independent leaf identifies a fresh record in one complete
chronological log by its ordinal among fresh records.  Its prefix includes
cached records, so it is suitable for the history-sensitive alpha label.  A
later V8 source theorem must construct the two cuts from the same root log;
this file neither supplies a scheduler run nor a probability statement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1400

namespace AspisV8Completion.FSV8AlphaCanonicalFreshCut

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters

variable {R : Type*}

def freshCount (fresh : R → Bool) : List R → Nat
  | [] => 0
  | record :: rest => if fresh record then freshCount fresh rest + 1
    else freshCount fresh rest

def pickFreshFrom (fresh : R → Bool) :
    List R → List R → Nat → Option (List R × R × List R)
  | _history, [], _ordinal => none
  | history, record :: rest, ordinal =>
      if fresh record then
        match ordinal with
        | 0 => some (history, record, rest)
        | next + 1 => pickFreshFrom fresh (history ++ [record]) rest next
      else pickFreshFrom fresh (history ++ [record]) rest ordinal

theorem pickFreshFrom_at_append
    (fresh : R → Bool) (before : List R) (current : R) (after : List R)
    (currentFresh : fresh current = true) :
    ∀ history,
      pickFreshFrom fresh history (before ++ current :: after)
        (freshCount fresh before) = some (history ++ before, current, after) := by
  induction before with
  | nil =>
      intro history
      simp [freshCount, pickFreshFrom, currentFresh]
  | cons record rest ih =>
      intro history
      cases recordFresh : fresh record <;>
        simp [freshCount, pickFreshFrom, recordFresh, ih, List.append_assoc]

structure IsFreshCut (fresh : R → Bool) (whole : List R) (ordinal : Nat)
    (before : List R) (current : R) (after : List R) : Prop where
  split : whole = before ++ current :: after
  selected : fresh current = true
  count : freshCount fresh before = ordinal

theorem fresh_cut_unique
    (fresh : R → Bool) (whole left right leftTail rightTail : List R)
    (leftRecord rightRecord : R)
    (leftSplit : whole = left ++ leftRecord :: leftTail)
    (rightSplit : whole = right ++ rightRecord :: rightTail)
    (leftFresh : fresh leftRecord = true)
    (rightFresh : fresh rightRecord = true)
    (sameOrdinal : freshCount fresh left = freshCount fresh right) :
    (left, leftRecord, leftTail) = (right, rightRecord, rightTail) := by
  have leftPick :=
    pickFreshFrom_at_append fresh left leftRecord leftTail leftFresh []
  have rightPick :=
    pickFreshFrom_at_append fresh right rightRecord rightTail rightFresh []
  simp only [List.nil_append] at leftPick rightPick
  rw [← leftSplit, sameOrdinal] at leftPick
  rw [← rightSplit] at rightPick
  exact Option.some.inj (leftPick.symm.trans rightPick)

theorem fresh_cut_labels_equal {Slot : Type*}
    (fresh : R → Bool) (label : List R → R → Slot)
    (whole : List R) (ordinal : Nat)
    (left right leftTail rightTail : List R) (leftRecord rightRecord : R)
    (leftCut : IsFreshCut fresh whole ordinal left leftRecord leftTail)
    (rightCut : IsFreshCut fresh whole ordinal right rightRecord rightTail) :
    label left leftRecord = label right rightRecord := by
  have exactCut := fresh_cut_unique fresh whole left right leftTail rightTail
    leftRecord rightRecord leftCut.split rightCut.split leftCut.selected
    rightCut.selected (leftCut.count.trans rightCut.count.symm)
  have beforeExact : left = right := congrArg Prod.fst exactCut
  have recordExact : leftRecord = rightRecord :=
    congrArg (fun triple : List R × R × List R => triple.2.1) exactCut
  rw [beforeExact, recordExact]

def recordFresh (record : QueryRecord) : Bool :=
  decide (record.origin = .fresh)

def recordAlphaLabel (round : Fin 4)
    (before : List QueryRecord) (record : QueryRecord) :
    Option RelationAlphaDuplexSlot :=
  if record.actor = .verifier then
    relationAlphaPreferredSlotFromHistory round before record.input
  else none

theorem alpha_label_equal_of_same_fresh_ordinal
    (round : Fin 4) (fullHistory : List QueryRecord) (ordinal : Nat)
    (schedulerBefore sourceBefore schedulerAfter sourceAfter : List QueryRecord)
    (schedulerRecord sourceRecord : QueryRecord)
    (schedulerCut : IsFreshCut recordFresh fullHistory ordinal
      schedulerBefore schedulerRecord schedulerAfter)
    (sourceCut : IsFreshCut recordFresh fullHistory ordinal
      sourceBefore sourceRecord sourceAfter) :
    recordAlphaLabel round schedulerBefore schedulerRecord =
      recordAlphaLabel round sourceBefore sourceRecord := by
  exact fresh_cut_labels_equal recordFresh (recordAlphaLabel round)
    fullHistory ordinal schedulerBefore sourceBefore schedulerAfter sourceAfter
    schedulerRecord sourceRecord schedulerCut sourceCut

theorem alpha_phase_record_origin_irrelevant
    (round : Fin 4) (phase : RelationAlphaHistoryPhase)
    (record : QueryRecord) (origin : AnswerOrigin) :
    phase.afterVerifierRecord round { record with origin := origin } =
      phase.afterVerifierRecord round record := by
  rfl

#print axioms fresh_cut_unique
#print axioms fresh_cut_labels_equal
#print axioms alpha_label_equal_of_same_fresh_ordinal

end AspisV8Completion.FSV8AlphaCanonicalFreshCut
