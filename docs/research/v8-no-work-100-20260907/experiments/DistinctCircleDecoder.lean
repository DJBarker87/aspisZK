import AspisFormal.K1.V7Tag73IncrementalSamplerControl

/-! Literal bounded distinct-second-circle wrapper around the existing
three-attempt secure-circle prefix decoder. Inner failures abort, only
successful duplicate points consume another outer attempt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.DistinctCircleDecoder
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl

def decodeDistinctPrefix (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) :
    Nat → List Digest256 → Option OrdinaryPrefixDecode
  | 0, _ => none
  | attempts+1, blocks => do
      let decoded ← decodeSecureCirclePrefix circleMap 3 blocks
      match circleMap decoded.value with
      | none => none
      | some point =>
          if point = firstPoint then
            decodeDistinctPrefix circleMap firstPoint attempts decoded.remainingBlocks
          else pure decoded

/-- The extra map match is not an extra assumption: success of the
existing inner decoder itself establishes a successful map output. -/
theorem circle_success_has_point (circleMap : SecureCircleParameterMap)
    (attempts : Nat) (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeSecureCirclePrefix circleMap attempts blocks = some decoded) :
    ∃ point, circleMap decoded.value = some point := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeSecureCirclePrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeSecureCirclePrefix, firstRun] at run
      | some first =>
          cases mapped : circleMap first.value with
          | none =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              exact ih first.remainingBlocks decoded run
          | some point =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              subst decoded
              exact ⟨point, mapped⟩

theorem inner_failure_aborts (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (attempts : Nat) (blocks : List Digest256)
    (failure : decodeSecureCirclePrefix circleMap 3 blocks = none) :
    decodeDistinctPrefix circleMap firstPoint (attempts+1) blocks = none := by
  simp [decodeDistinctPrefix, failure]

theorem success_distinct (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (attempts : Nat)
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeDistinctPrefix circleMap firstPoint attempts blocks = some decoded) :
    ∃ point, circleMap decoded.value = some point ∧ point ≠ firstPoint := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeDistinctPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeSecureCirclePrefix circleMap 3 blocks with
      | none => simp [decodeDistinctPrefix, firstRun] at run
      | some first =>
          cases mapped : circleMap first.value with
          | none => simp [decodeDistinctPrefix, firstRun, mapped] at run
          | some point =>
              by_cases equal : point = firstPoint
              · simp [decodeDistinctPrefix, firstRun, mapped, equal] at run
                exact ih first.remainingBlocks decoded run
              · simp [decodeDistinctPrefix, firstRun, mapped, equal] at run
                subst decoded
                exact ⟨point, mapped, equal⟩

/-- Every successful accepted prefix is insensitive to an unread block
suffix. In particular, no unused future retry can change its choice. -/
theorem append_of_some (circleMap : SecureCircleParameterMap)
    (firstPoint : SecureCirclePointBytes) (attempts : Nat)
    (blocks suffix : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeDistinctPrefix circleMap firstPoint attempts blocks = some decoded) :
    decodeDistinctPrefix circleMap firstPoint attempts (blocks ++ suffix) =
      some (appendOrdinaryRemaining decoded suffix) := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeDistinctPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeSecureCirclePrefix circleMap 3 blocks with
      | none => simp [decodeDistinctPrefix, firstRun] at run
      | some first =>
          have extended := decodeSecureCirclePrefix_append_of_some circleMap 3
            blocks suffix first firstRun
          cases mapped : circleMap first.value with
          | none => simp [decodeDistinctPrefix, firstRun, mapped] at run
          | some point =>
              by_cases equal : point = firstPoint
              · simp [decodeDistinctPrefix, firstRun, mapped, equal] at run
                have recursive := ih first.remainingBlocks decoded run
                simpa [decodeDistinctPrefix, extended, appendOrdinaryRemaining,
                  mapped, equal] using recursive
              · simp [decodeDistinctPrefix, firstRun, mapped, equal] at run
                subst decoded
                simp [decodeDistinctPrefix, extended, appendOrdinaryRemaining, mapped, equal]

#print axioms circle_success_has_point
#print axioms inner_failure_aborts
#print axioms success_distinct
#print axioms append_of_some
end
end AspisV8.DistinctCircleDecoder
