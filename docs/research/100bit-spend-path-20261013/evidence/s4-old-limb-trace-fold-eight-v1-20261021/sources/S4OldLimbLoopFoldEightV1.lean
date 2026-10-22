import S4OldLimbLoopReverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsOldLimbLoopFoldEightV1
open AspisR1FastDotsNewOuterLimbLoopSegmentV1
abbrev Usize := Std.Usize
abbrev U64 := UScalar UScalarTy.U64
private abbrev Range := core.ops.range.Range Usize
private abbrev FoldTrace := AspisR1FastDotsOldLimbLoopReverseV1.FoldTrace
private theorem result_bind_assoc {α β γ : Type} (m : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do let y ← (do let x ← m; f x); g y) =
      (do let x ← m; let y ← f x; g y) := by
  cases m <;> rfl
theorem foldEight_eq_foldSegment_chain (sums limbs : Array U64 8#usize) :
    foldEight sums limbs = (do
      let l1 ← foldSegment sums limbs 0#usize
      let l2 ← foldSegment sums l1 1#usize
      let l3 ← foldSegment sums l2 2#usize
      let l4 ← foldSegment sums l3 3#usize
      let l5 ← foldSegment sums l4 4#usize
      let l6 ← foldSegment sums l5 5#usize
      let l7 ← foldSegment sums l6 6#usize
      foldSegment sums l7 7#usize) := by
  unfold foldEight
  simp only [foldSegment, result_bind_assoc]
private theorem range_eq_components (iter : Range) (start stop : Usize)
    (hs : iter.start.val = start.val) (he : iter.end.val = stop.val) :
    iter = { start := start, «end» := stop } := by
  cases iter with
  | mk actualStart actualEnd =>
    have hs' : actualStart = start := UScalar.eq_of_val_eq hs
    have he' : actualEnd = stop := UScalar.eq_of_val_eq he
    subst actualStart
    subst actualEnd
    rfl
theorem trace_eight_segment_successes
    (sums initial out : Array U64 8#usize)
    (trace : FoldTrace sums { start := 0#usize, «end» := 8#usize } initial out) :
    ∃ l1 l2 l3 l4 l5 l6 l7,
      foldSegment sums initial 0#usize = .ok l1 ∧
      foldSegment sums l1 1#usize = .ok l2 ∧
      foldSegment sums l2 2#usize = .ok l3 ∧
      foldSegment sums l3 3#usize = .ok l4 ∧
      foldSegment sums l4 4#usize = .ok l5 ∧
      foldSegment sums l5 5#usize = .ok l6 ∧
      foldSegment sums l6 6#usize = .ok l7 ∧
      foldSegment sums l7 7#usize = .ok out := by
  let r0 : Range := { start := 0#usize, «end» := 8#usize }
  let r1 : Range := { start := 1#usize, «end» := 8#usize }
  let r2 : Range := { start := 2#usize, «end» := 8#usize }
  let r3 : Range := { start := 3#usize, «end» := 8#usize }
  let r4 : Range := { start := 4#usize, «end» := 8#usize }
  let r5 : Range := { start := 5#usize, «end» := 8#usize }
  let r6 : Range := { start := 6#usize, «end» := 8#usize }
  let r7 : Range := { start := 7#usize, «end» := 8#usize }
  let r8 : Range := { start := 8#usize, «end» := 8#usize }
  change FoldTrace sums r0 initial out at trace
  cases trace with
  | finish hge heq =>
      have hfalse : ¬ (0#usize).val ≥ (8#usize).val := by scalar_tac
      exact False.elim (hfalse (by simpa [r0] using hge))
  | @step it0 itN0 st0 mid0 fin0 hlt0 hs0 he0 hf0 tail0 =>
      let l1 := mid0
      have hseg0 : foldSegment sums initial 0#usize = .ok l1 := by
        change foldSegment sums initial 0#usize = .ok mid0 at hf0
        exact hf0
      have hnextStart0 : itN0.start.val = (1#usize).val := by
        have hv := hs0
        have hsimp : itN0.start.val = (0#usize).val + 1 := by simpa [r0] using hv
        scalar_tac
      have hnextEnd0 : itN0.end.val = (8#usize).val := by
        rw [he0]
      have hrange1 : itN0 = r1 := by
        exact range_eq_components itN0 (1#usize) (8#usize) hnextStart0 hnextEnd0
      subst itN0
      cases tail0 with
        | finish hge heq =>
            have hfalse : ¬ (1#usize).val ≥ (8#usize).val := by scalar_tac
            exact False.elim (hfalse (by simpa [r1] using hge))
        | @step it1 itN1 st1 mid1 fin1 hlt1 hs1 he1 hf1 tail1 =>
          let l2 := mid1
          have hseg1 : foldSegment sums l1 1#usize = .ok l2 := by
            change foldSegment sums l1 1#usize = .ok mid1 at hf1
            exact hf1
          have hnextStart1 : itN1.start.val = (2#usize).val := by
            have hv := hs1
            have hsimp : itN1.start.val = (1#usize).val + 1 := by simpa [r1] using hv
            scalar_tac
          have hnextEnd1 : itN1.end.val = (8#usize).val := by
            rw [he1]
          have hrange2 : itN1 = r2 := by
            exact range_eq_components itN1 (2#usize) (8#usize) hnextStart1 hnextEnd1
          subst itN1
          cases tail1 with
            | finish hge heq =>
                have hfalse : ¬ (2#usize).val ≥ (8#usize).val := by scalar_tac
                exact False.elim (hfalse (by simpa [r2] using hge))
            | @step it2 itN2 st2 mid2 fin2 hlt2 hs2 he2 hf2 tail2 =>
              let l3 := mid2
              have hseg2 : foldSegment sums l2 2#usize = .ok l3 := by
                change foldSegment sums l2 2#usize = .ok mid2 at hf2
                exact hf2
              have hnextStart2 : itN2.start.val = (3#usize).val := by
                have hv := hs2
                have hsimp : itN2.start.val = (2#usize).val + 1 := by simpa [r2] using hv
                scalar_tac
              have hnextEnd2 : itN2.end.val = (8#usize).val := by
                rw [he2]
              have hrange3 : itN2 = r3 := by
                exact range_eq_components itN2 (3#usize) (8#usize) hnextStart2 hnextEnd2
              subst itN2
              cases tail2 with
                | finish hge heq =>
                    have hfalse : ¬ (3#usize).val ≥ (8#usize).val := by scalar_tac
                    exact False.elim (hfalse (by simpa [r3] using hge))
                | @step it3 itN3 st3 mid3 fin3 hlt3 hs3 he3 hf3 tail3 =>
                  let l4 := mid3
                  have hseg3 : foldSegment sums l3 3#usize = .ok l4 := by
                    change foldSegment sums l3 3#usize = .ok mid3 at hf3
                    exact hf3
                  have hnextStart3 : itN3.start.val = (4#usize).val := by
                    have hv := hs3
                    have hsimp : itN3.start.val = (3#usize).val + 1 := by simpa [r3] using hv
                    scalar_tac
                  have hnextEnd3 : itN3.end.val = (8#usize).val := by
                    rw [he3]
                  have hrange4 : itN3 = r4 := by
                    exact range_eq_components itN3 (4#usize) (8#usize) hnextStart3 hnextEnd3
                  subst itN3
                  cases tail3 with
                    | finish hge heq =>
                        have hfalse : ¬ (4#usize).val ≥ (8#usize).val := by scalar_tac
                        exact False.elim (hfalse (by simpa [r4] using hge))
                    | @step it4 itN4 st4 mid4 fin4 hlt4 hs4 he4 hf4 tail4 =>
                      let l5 := mid4
                      have hseg4 : foldSegment sums l4 4#usize = .ok l5 := by
                        change foldSegment sums l4 4#usize = .ok mid4 at hf4
                        exact hf4
                      have hnextStart4 : itN4.start.val = (5#usize).val := by
                        have hv := hs4
                        have hsimp : itN4.start.val = (4#usize).val + 1 := by simpa [r4] using hv
                        scalar_tac
                      have hnextEnd4 : itN4.end.val = (8#usize).val := by
                        rw [he4]
                      have hrange5 : itN4 = r5 := by
                        exact range_eq_components itN4 (5#usize) (8#usize) hnextStart4 hnextEnd4
                      subst itN4
                      cases tail4 with
                        | finish hge heq =>
                            have hfalse : ¬ (5#usize).val ≥ (8#usize).val := by scalar_tac
                            exact False.elim (hfalse (by simpa [r5] using hge))
                        | @step it5 itN5 st5 mid5 fin5 hlt5 hs5 he5 hf5 tail5 =>
                          let l6 := mid5
                          have hseg5 : foldSegment sums l5 5#usize = .ok l6 := by
                            change foldSegment sums l5 5#usize = .ok mid5 at hf5
                            exact hf5
                          have hnextStart5 : itN5.start.val = (6#usize).val := by
                            have hv := hs5
                            have hsimp : itN5.start.val = (5#usize).val + 1 := by simpa [r5] using hv
                            scalar_tac
                          have hnextEnd5 : itN5.end.val = (8#usize).val := by
                            rw [he5]
                          have hrange6 : itN5 = r6 := by
                            exact range_eq_components itN5 (6#usize) (8#usize) hnextStart5 hnextEnd5
                          subst itN5
                          cases tail5 with
                            | finish hge heq =>
                                have hfalse : ¬ (6#usize).val ≥ (8#usize).val := by scalar_tac
                                exact False.elim (hfalse (by simpa [r6] using hge))
                            | @step it6 itN6 st6 mid6 fin6 hlt6 hs6 he6 hf6 tail6 =>
                              let l7 := mid6
                              have hseg6 : foldSegment sums l6 6#usize = .ok l7 := by
                                change foldSegment sums l6 6#usize = .ok mid6 at hf6
                                exact hf6
                              have hnextStart6 : itN6.start.val = (7#usize).val := by
                                have hv := hs6
                                have hsimp : itN6.start.val = (6#usize).val + 1 := by simpa [r6] using hv
                                scalar_tac
                              have hnextEnd6 : itN6.end.val = (8#usize).val := by
                                rw [he6]
                              have hrange7 : itN6 = r7 := by
                                exact range_eq_components itN6 (7#usize) (8#usize) hnextStart6 hnextEnd6
                              subst itN6
                              cases tail6 with
                                | finish hge heq =>
                                    have hfalse : ¬ (7#usize).val ≥ (8#usize).val := by scalar_tac
                                    exact False.elim (hfalse (by simpa [r7] using hge))
                                | @step it7 itN7 st7 mid7 fin7 hlt7 hs7 he7 hf7 tail7 =>
                                  let l8 := mid7
                                  have hseg7 : foldSegment sums l7 7#usize = .ok l8 := by
                                    change foldSegment sums l7 7#usize = .ok mid7 at hf7
                                    exact hf7
                                  have hnextStart7 : itN7.start.val = (8#usize).val := by
                                    have hv := hs7
                                    have hsimp : itN7.start.val = (7#usize).val + 1 := by simpa [r7] using hv
                                    scalar_tac
                                  have hnextEnd7 : itN7.end.val = (8#usize).val := by
                                    rw [he7]
                                  have hrange8 : itN7 = r8 := by
                                    exact range_eq_components itN7 (8#usize) (8#usize) hnextStart7 hnextEnd7
                                  subst itN7
                                  cases tail7 with
                                    | finish hge heq =>
                                        have hlast : foldSegment sums l7 7#usize = .ok out := by
                                          have hout : out = mid7 := heq
                                          simpa [l8, hout] using hseg7
                                        exact ⟨l1,l2,l3,l4,l5,l6,l7,hseg0,hseg1,hseg2,hseg3,hseg4,hseg5,hseg6,hlast⟩
                                    | @step _ _ _ _ _ hlt8 _ _ _ _ =>
                                        have hbad : (8#usize).val < (8#usize).val := by
                                          simpa [hnextStart7, hnextEnd7] using hlt8
                                        omega

theorem old_limb_loop_success_foldEight
    (ops : Ops) (sums initial out : Array U64 8#usize)
    (hloop : LimbLoop ops { start := 0#usize, «end» := 8#usize } initial sums = .ok out) :
    foldEight sums initial = .ok out := by
  obtain ⟨trace⟩ := AspisR1FastDotsOldLimbLoopReverseV1.old_loop_success_eight_ordered
    ops sums initial out hloop
  obtain ⟨l1,l2,l3,l4,l5,l6,l7,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    trace_eight_segment_successes sums initial out trace
  rw [foldEight_eq_foldSegment_chain]
  simp only [h0,h1,h2,h3,h4,h5,h6,h7, bind_tc_ok]
#print axioms trace_eight_segment_successes
#print axioms old_limb_loop_success_foldEight
end AspisR1FastDotsOldLimbLoopFoldEightV1
