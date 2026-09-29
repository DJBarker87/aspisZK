import V7CallerCurrentReleaseR26TerminalDotComponents

/-!
# Terminal contribution sum as the maintained K1 candidate claim

The component-wise terminal formulas are identified with the dot product of
the four terminal values and the six-component K1 output-weight vector.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalDotModelIdentity

open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open V7CallerCurrentReleaseR26TerminalLineClaim
open V7CallerCurrentReleaseR26TerminalLineModel
open V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open AspisV5FriRelationCandidateBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalValueArray (values : Slice RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize
    [values.val[0]!, values.val[1]!, values.val[2]!, values.val[3]!]

theorem terminal_value_array_canonical
    (values : Slice RawQM31) (canonical : CanonicalSlice values)
    (length : values.length = 4) :
    V7CallerCurrentReleaseR26Qm31SumProducts4Semantics.GeneratedCanonicalQM31Array4
      (terminalValueArray values) := by
  intro index indexBound
  have c0 := canonical 0 (by simpa [length])
  have c1 := canonical 1 (by simpa [length])
  have c2 := canonical 2 (by simpa [length])
  have c3 := canonical 3 (by simpa [length])
  interval_cases index
  · change V7CallerCurrentReleaseR26FieldBridge.GeneratedCanonicalQM31
      values.val[0]!
    exact c0
  · change V7CallerCurrentReleaseR26FieldBridge.GeneratedCanonicalQM31
      values.val[1]!
    exact c1
  · change V7CallerCurrentReleaseR26FieldBridge.GeneratedCanonicalQM31
      values.val[2]!
    exact c2
  · change V7CallerCurrentReleaseR26FieldBridge.GeneratedCanonicalQM31
      values.val[3]!
    exact c3

theorem terminal_value_read
    (values : Slice RawQM31) (index : Std.Usize)
    (bound : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem multilinear_terminal_claim
    (scale p0 p1 : RawQM31) (values : Slice RawQM31) :
    multilinearTerminal scale p0 p1 values =
      candidateClaim
        (structuredComponentWeights .multilinear 1 scale [p0, p1])
        (terminalValues values) := by
  change multilinearTerminal scale p0 p1 values =
    ∑ index : Fin 4,
      terminalValues values index *
        (exactRaw scale *
          structuredBasisWeightNat .multilinear [p0, p1] 1 index.val)
  rw [Fin.sum_univ_four]
  unfold multilinearTerminal terminalValues
    structuredBasisWeightNat structuredPairWeights
  simp [structuredBasisWeightNat]
  ring

private theorem tensor_terminal_claim
    (scale f0 f1 : RawQM31) (values : Slice RawQM31) :
    tensorTerminal scale f0 f1 values =
      candidateClaim
        (structuredComponentWeights .tensor 1 scale [f0, f1])
        (terminalValues values) := by
  change tensorTerminal scale f0 f1 values =
    ∑ index : Fin 4,
      terminalValues values index *
        (exactRaw scale *
          structuredBasisWeightNat .tensor [f0, f1] 1 index.val)
  rw [Fin.sum_univ_four]
  unfold tensorTerminal terminalValues
    structuredBasisWeightNat structuredPairWeights
  simp [structuredBasisWeightNat]
  ring

private theorem line_terminal_claim
    (scales : Slice RawQM31) (xs : Slice RawM31) (deferred : Nat)
    (values : Slice RawQM31) :
    terminalLineModelDot scales xs deferred (terminalValueArray values) =
      candidateClaim (lineBatchComponentWeights 1 scales xs deferred)
        (terminalValues values) := by
  have weightsEq :
      lineBatchComponentWeights 1 scales xs deferred =
        lineBatchWeightsOne scales xs deferred := by
    funext index
    rfl
  rw [weightsEq]
  unfold terminalLineModelDot candidateClaim
  apply Finset.sum_congr rfl
  intro index indexMem
  fin_cases index
  · change exactRaw values.val[0]! * _ = exactRaw values.val[0]! * _
    rfl
  · change exactRaw values.val[1]! * _ = exactRaw values.val[1]! * _
    rfl
  · change exactRaw values.val[2]! * _ = exactRaw values.val[2]! * _
    rfl
  · change exactRaw values.val[3]! * _ = exactRaw values.val[3]! * _
    rfl

private theorem candidateClaim_sumSix
    (a b c d e f : Fin 4 → ModelQM31)
    (values : Fin 4 → ModelQM31) :
    candidateClaim (sumSix a b c d e f) values =
      candidateClaim a values + candidateClaim b values +
      candidateClaim c values + candidateClaim d values +
      candidateClaim e values + candidateClaim f values := by
  unfold candidateClaim sumSix
  simp only [mul_add, Finset.sum_add_distrib]

theorem terminal_six_sum_eq_candidate
    (mScale0 mScale1 tScale0 tScale1 : RawQM31)
    (mPoint0 mPoint1 tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (g0 g1 g2 g3 : RawQM31)
    (lineScales : Slice RawQM31) (lineXs : Slice RawM31)
    (deferred : Nat) (values : Slice RawQM31)
    (mPoint0Exact : mPoint0.val = [mPoint0.val[0]!, mPoint0.val[1]!])
    (mPoint1Exact : mPoint1.val = [mPoint1.val[0]!, mPoint1.val[1]!])
    (tFactors0Exact :
      tFactors0.val = [tFactors0.val[0]!, tFactors0.val[1]!])
    (tFactors1Exact :
      tFactors1.val = [tFactors1.val[0]!, tFactors1.val[1]!]) :
    terminalLineModelDot lineScales lineXs deferred
          (terminalValueArray values) +
        multilinearTerminal mScale0 mPoint0.val[0]! mPoint0.val[1]!
          values +
        multilinearTerminal mScale1 mPoint1.val[0]! mPoint1.val[1]!
          values +
        candidateClaim
          (representedGroupedWeights releasedRowGroups4
            (releasedFourValues g0 g1 g2 g3))
          (terminalValues values) +
        tensorTerminal tScale0 tFactors0.val[0]! tFactors0.val[1]!
          values +
        tensorTerminal tScale1 tFactors1.val[0]! tFactors1.val[1]!
          values =
      candidateClaim
        (sumSix
          (structuredComponentWeights .multilinear 1 mScale0 mPoint0.val)
          (structuredComponentWeights .multilinear 1 mScale1 mPoint1.val)
          (representedGroupedWeights releasedRowGroups4
            (releasedFourValues g0 g1 g2 g3))
          (structuredComponentWeights .tensor 1 tScale0 tFactors0.val)
          (structuredComponentWeights .tensor 1 tScale1 tFactors1.val)
          (lineBatchComponentWeights 1 lineScales lineXs deferred))
        (terminalValues values) := by
  calc
    _ = candidateClaim
          (structuredComponentWeights .multilinear 1 mScale0 mPoint0.val)
          (terminalValues values) +
        candidateClaim
          (structuredComponentWeights .multilinear 1 mScale1 mPoint1.val)
          (terminalValues values) +
        candidateClaim
          (representedGroupedWeights releasedRowGroups4
            (releasedFourValues g0 g1 g2 g3))
          (terminalValues values) +
        candidateClaim
          (structuredComponentWeights .tensor 1 tScale0 tFactors0.val)
          (terminalValues values) +
        candidateClaim
          (structuredComponentWeights .tensor 1 tScale1 tFactors1.val)
          (terminalValues values) +
        candidateClaim
          (lineBatchComponentWeights 1 lineScales lineXs deferred)
          (terminalValues values) := by
      rw [mPoint0Exact, mPoint1Exact, tFactors0Exact, tFactors1Exact]
      rw [multilinear_terminal_claim, multilinear_terminal_claim,
        tensor_terminal_claim, tensor_terminal_claim, line_terminal_claim]
      simp
      ring
    _ = candidateClaim
          (sumSix
            (structuredComponentWeights .multilinear 1 mScale0 mPoint0.val)
            (structuredComponentWeights .multilinear 1 mScale1 mPoint1.val)
            (representedGroupedWeights releasedRowGroups4
              (releasedFourValues g0 g1 g2 g3))
            (structuredComponentWeights .tensor 1 tScale0 tFactors0.val)
            (structuredComponentWeights .tensor 1 tScale1 tFactors1.val)
            (lineBatchComponentWeights 1 lineScales lineXs deferred))
          (terminalValues values) :=
      by
        unfold candidateClaim sumSix
        simp only [mul_add, Finset.sum_add_distrib]
        rfl

#print axioms terminal_value_array_canonical
#print axioms terminal_value_read
#print axioms terminal_six_sum_eq_candidate

end V7CallerCurrentReleaseR26TerminalDotModelIdentity
