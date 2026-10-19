import BatchedWeightsCallerSafeCadenceV4
import BatchedWeightsSelectedPhaseBoundV11
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSafeRowsFrameV1
open AspisR1BatchedWeightsExtraction
open BatchedWeightsCallerSafeCadenceV4
open AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := BatchedWeightsCallerSafeCadenceV4.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsCallerSafeCadenceV4.Q
abbrev M := BatchedWeightsCallerSafeCadenceV4.M

theorem safeRows_length (rows : List RowVisit) (initial final : BW)
    (hsafe : SafeRows rows initial final) : final.raw.length = initial.raw.length := by
  induction rows generalizing initial final with
  | nil => cases hsafe; rfl
  | cons head rest ih =>
      cases hsafe with
      | cons _ _ _ _ hhead htail =>
          obtain ⟨mid,hpush,hterms,hlen,hframe⟩ :=
            BatchedWeightsSelectedPushGeneralFrameV1.selected_push_preserves_outer_frame
              head.index initial head.power head.basis hhead.indexValid hhead.rawBound
              hhead.power0a hhead.power0b hhead.power1a hhead.power1b hhead.basis
          have htail' := htail mid hpush
          have htailLength := ih mid final htail'
          change final.raw.val.length = mid.raw.val.length at htailLength
          change mid.raw.val.length = initial.raw.val.length at hlen
          calc final.raw.val.length = mid.raw.val.length := htailLength
            _ = initial.raw.val.length := hlen

/-- Generated pushes preserve the complete row array at any row absent from
the remaining visit list. The proof uses the actual vector-set frame theorem. -/
theorem safeRows_unvisited_row_eq
    (rows : List RowVisit) (initial final : BW) (target : Usize)
    (htarget : target.val < initial.raw.length)
    (hsafe : SafeRows rows initial final)
    (hnot : ∀ v, v ∈ rows → v.index.val ≠ target.val)
    (k : Usize) (hk : k.val < 4) :
    cellAt final target (by rw [safeRows_length rows initial final hsafe]; exact htarget) k hk =
      cellAt initial target htarget k hk := by
  induction rows generalizing initial final with
  | nil => cases hsafe; rfl
  | cons head rest ih =>
      cases hsafe with
      | cons _ _ _ _ hhead htail =>
          have hnotHead : head.index.val ≠ target.val := hnot head (by simp)
          obtain ⟨mid,hpush,hterms,hlen,hframe⟩ :=
            BatchedWeightsSelectedPushGeneralFrameV1.selected_push_preserves_outer_frame
              head.index initial head.power head.basis hhead.indexValid hhead.rawBound
              hhead.power0a hhead.power0b hhead.power1a hhead.power1b hhead.basis
          have htargetMid : target.val < mid.raw.val.length := by
            change target.val < mid.raw.val.length
            rw [hlen]
            exact htarget
          have hrowFrame : mid.raw.val[target.val]'htargetMid =
              initial.raw.val[target.val]'htarget := hframe hlen target htarget hnotHead.symm
          have htailSafe := htail mid hpush
          have hnotTail : ∀ v, v ∈ rest → v.index.val ≠ target.val := by
            intro v hv
            exact hnot v (by simp [hv])
          have htailEq := ih mid final htargetMid htailSafe hnotTail
          have hfinalLen : final.raw.val.length = mid.raw.val.length := by
            change final.raw.val.length = mid.raw.val.length
            exact safeRows_length rest mid final htailSafe
          have hfin : target.val < final.raw.val.length := by
            change target.val < final.raw.val.length
            rw [hfinalLen]
            exact htargetMid
          have hmidCell : cellAt mid target htargetMid k hk =
              cellAt initial target htarget k hk := by
            change ((rowAt mid target htargetMid).val[k.val]'
              (by simpa [(rowAt mid target htargetMid).property] using hk)).val =
              ((rowAt initial target htarget).val[k.val]'
              (by simpa [(rowAt initial target htarget).property] using hk)).val
            exact congrArg (fun row : Array Std.U64 4#usize =>
              (row.val[k.val]'(by simpa [row.property] using hk)).val) (by
                change mid.raw.val[target.val]'htargetMid = initial.raw.val[target.val]'htarget
                exact hrowFrame)
          have htailCell := htailEq
          calc
            cellAt final target hfin k hk =
                cellAt mid target htargetMid k hk := htailCell
            _ = cellAt initial target htarget k hk := hmidCell

#print axioms safeRows_length
#print axioms safeRows_unvisited_row_eq
end BatchedWeightsSafeRowsFrameV1
