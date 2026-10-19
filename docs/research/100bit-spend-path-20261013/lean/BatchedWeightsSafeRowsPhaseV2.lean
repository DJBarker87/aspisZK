import BatchedWeightsSafeRowsFrameV6
import BatchedWeightsSelectedPhaseBoundV11
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSafeRowsPhaseV1
open AspisR1BatchedWeightsExtraction
open BatchedWeightsCallerSafeCadenceV4
abbrev BW := BatchedWeightsCallerSafeCadenceV4.BW
abbrev Usize := UScalar UScalarTy.Usize

/-- Every row selected during a duplicate-free safe traversal retains its
next-phase (or post-flush) bound in the final state. Later pushes preserve it
by the actual nonselected-row frame theorem. -/
theorem safeRows_member_next_phase_bound
    (rows : List RowVisit) (initial final : BW) (target : Usize)
    (htarget : target.val < initial.raw.length)
    (hsafe : SafeRows rows initial final)
    (hnodup : (rows.map fun v => v.index.val).Nodup)
    (hmem : target.val ∈ rows.map fun v => v.index.val) :
    ∀ k : Usize, ∀ hk : k.val < 4,
      AspisR1BatchedWeightsPushLoopAllPrefixV11.cellAt final target
        (by rw [BatchedWeightsSafeRowsFrameV1.safeRows_length rows initial final hsafe]; exact htarget)
        k hk < 2^34 + ((initial.terms.val + 1) % 4) * AspisR1BatchedAllPrefix.cap := by
  induction rows generalizing initial final with
  | nil => simp at hmem
  | cons head rest ih =>
      cases hsafe with
      | cons _ _ _ _ hhead htail =>
          have hparts : target.val = head.index.val ∨
              target.val ∈ rest.map fun v => v.index.val := by
            simpa using hmem
          obtain ⟨mid,hpush,hterms,hlen,hframe⟩ :=
            BatchedWeightsSelectedPushGeneralFrameV1.selected_push_preserves_outer_frame
              head.index initial head.power head.basis hhead.indexValid hhead.rawBound
              hhead.power0a hhead.power0b hhead.power1a hhead.power1b hhead.basis
          have htailSafe := htail mid hpush
          have hnodupParts := List.nodup_cons.mp hnodup
          have hnodupTail : (rest.map fun v => v.index.val).Nodup := hnodupParts.2
          have hmidIndex : target.val < mid.raw.length := by
            change target.val < mid.raw.val.length
            rw [hlen]
            exact htarget
          have hfinalIndex : target.val < final.raw.length := by
            rw [BatchedWeightsSafeRowsFrameV1.safeRows_length rest mid final htailSafe]
            exact hmidIndex
          rcases hparts with hheadEq | htailMem
          · have htargetEq : target = head.index := UScalar.eq_of_val_eq hheadEq
            subst target
            have hmidBound := BatchedWeightsSelectedPhaseBoundV10.selected_cell_next_phase_bound
              head.index initial mid head.power head.basis hhead.indexValid hhead.rawBound
              hhead.power0a hhead.power0b hhead.power1a hhead.power1b hhead.basis hpush
            have hnotTail : ∀ v, v ∈ rest → v.index.val ≠ head.index.val := by
              intro v hv heq
              have hbad : head.index.val ∈ rest.map fun u => u.index.val := by
                apply List.mem_map.mpr
                exact ⟨v,hv,heq⟩
              exact hnodupParts.1 hbad
            intro k hk
            have hsame := BatchedWeightsSafeRowsFrameV1.safeRows_unvisited_row_eq
              rest mid final head.index hmidIndex htailSafe hnotTail k hk
            rw [hsame]
            exact hmidBound.2 k hk
          · have hih := ih mid final hmidIndex htailSafe hnodupTail htailMem
            have htermsVal : mid.terms.val = initial.terms.val := congrArg UScalar.val hterms
            intro k hk
            have hbound := hih k hk
            rw [htermsVal] at hbound
            exact hbound

#print axioms safeRows_member_next_phase_bound
end BatchedWeightsSafeRowsPhaseV1
