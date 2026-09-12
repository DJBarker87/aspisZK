import FSAdaptiveFreshPairMass

/-!
The exact fresh law for one source squeeze, with all cache-reuse alternatives
left visible.

One squeeze makes two chronological oracle requests.  The first is the
33-byte target request `digest ++ [1]`; an earlier occurrence places the
entire 256-bit digest in the explicit prior-target set.  The second is the
distinct 33-byte state-advance request `digest ++ [2]`; an earlier occurrence
is retained separately because it is not a target request and must not be
silently treated as another fresh coin.

This is a prefix classifier and exact conditional mass statement.  It does
not bound either prior alternative or compose retries.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSSourceSqueezeFreshOrPrior
open scoped BigOperators
open FSOracleExecution FSExposureOrder FSFirstFresh FSAdaptiveFreshPairMass

noncomputable section

abbrev Block := FSExposureOrder.Block
abbrev Oracle := FSFirstFresh.Oracle

/-- Extract the digest named by a literal source state-advance request.  This
is deliberately separate from `FSExposureOrder.targetOf`, whose suffix is 1
and whose event is the output request. -/
def advanceTargetOf (input : List UInt8) : Option (List UInt8) :=
  if input.length = 33 ∧ input.getLast? = some 2 then some (input.take 32) else none

def priorAdvanceTargets (log : FSExposureOrder.Log) (cut : Nat) : List (List UInt8) :=
  ((inputs (log.take cut)).eraseDups).filterMap advanceTargetOf

theorem advanceTargetOf_advance (digest : Block) :
    advanceTargetOf (advanceInput digest) = some (blockBytes digest) := by
  simp [advanceTargetOf, advanceInput, blockBytes]

theorem advance_target_count (log : FSExposureOrder.Log) (cut : Nat) :
    (priorAdvanceTargets log cut).length ≤
      (inputs (log.take cut)).eraseDups.length :=
  List.length_filterMap_le ..

theorem advance_target_of_seen (log : FSExposureOrder.Log) (digest : Block)
    (seen : advanceInput digest ∈ inputs log) :
    blockBytes digest ∈ priorAdvanceTargets log log.length := by
  apply List.mem_filterMap.mpr
  refine ⟨advanceInput digest, ?_, advanceTargetOf_advance digest⟩
  apply List.mem_eraseDups.mpr
  simpa [inputs] using seen

/-- At an arbitrary chronological prefix, the literal source squeeze is
fresh at both requests, or the exact prior reuse is exposed.  In particular,
the second request is not hidden inside the digest-target alternative. -/
theorem unseen_or_prior (state : Oracle) (digest : Block) :
    (outputInput digest ∉ inputs state.log ∧
      advanceInput digest ∉ inputs state.log) ∨
    blockBytes digest ∈ priorTargets state.log state.log.length ∨
    blockBytes digest ∈ priorAdvanceTargets state.log state.log.length := by
  by_cases outputSeen : outputInput digest ∈ inputs state.log
  · right
    left
    apply target_of_earlier_squeeze state.log digest state.log.length outputSeen
    have within := List.idxOf_lt_length_of_mem outputSeen
    simpa only [firstExposure, outputInput, inputs, List.length_map] using within
  · by_cases advanceSeen : advanceInput digest ∈ inputs state.log
    · exact Or.inr (Or.inr (advance_target_of_seen state.log digest advanceSeen))
    · exact Or.inl ⟨outputSeen, advanceSeen⟩

/-- Exact fresh mass for the actual adaptive two-request squeeze, or an
explicit cache-reuse branch.  `ValidHistory` is the constructed interpreter
invariant used to turn log absence into cache absence; no independence is
inferred from the final transcript or from domain-separation labels. -/
theorem uniform_targets_or_prior
    (tape : Nat → Block) (state : Oracle) (digest firstTarget secondTarget : Block)
    (valid : ValidHistory state) :
    ((∑ first : Block, ∑ second : Block,
        if (adaptivePair tape state (outputInput digest)
            (fun _ => advanceInput digest) (first, second)).1 =
            (firstTarget, secondTarget)
        then (1 : ℚ) else 0) / (Fintype.card Block : ℚ) ^ 2 =
          1 / (Fintype.card Block : ℚ) ^ 2) ∨
    blockBytes digest ∈ priorTargets state.log state.log.length ∨
    blockBytes digest ∈ priorAdvanceTargets state.log state.log.length := by
  rcases unseen_or_prior state digest with fresh | prior
  · exact Or.inl (sourceSqueeze_uniform_targets tape state digest
      firstTarget secondTarget valid fresh.1 fresh.2)
  · exact Or.inr prior

#print axioms unseen_or_prior
#print axioms uniform_targets_or_prior
#print axioms advance_target_count

end
end AspisV8Completion.FSSourceSqueezeFreshOrPrior
