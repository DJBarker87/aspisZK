import S1OwnedQueryPairsSourceFinishV1
import S1OwnedQueryPairsIndexModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result

/-- FULL Result equality to the query decoder already installed in preparation.
No successful execution, scan law, or model-correctness premise remains. -/
theorem reference_eq_source (blocks advances : Blocks) :
    AspisR1Query31Transcript.queries_from_pairs_with_scan
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      (project initial) blocks advances=adapt (pairs_reference blocks advances) := by
  unfold AspisR1Query31Transcript.queries_from_pairs_with_scan pairs_reference adapt
  conv => rhs; rw [atBlock_call advances 7#usize (by decide)]
  simp only [bind_tc_ok,bind_assoc_eq]
  obtain ⟨s0,next0,stop0,own0,v0,src0,sel0⟩ :=
    step_source initial (atBlock advances 7#usize (by decide)) 0#usize blocks advances (by decide) initial_valid
  dsimp only [initial] at own0
  rw [sel0] at own0
  rw [atBlock_call blocks 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [src0,own0]
  simp only [bind_tc_ok]
  cases stop0 with
  | true =>
    dsimp only
    simp only [if_true]
    exact finish_source s0 advances 0#usize (by decide)
  | false =>
    dsimp only
    simp only [Bool.false_eq_true,if_false]
    obtain ⟨s1,next1,stop1,own1,v1,src1,sel1⟩ :=
      step_source s0 (atBlock advances 7#usize (by decide)) 1#usize blocks advances (by decide) v0
    rw [sel1] at own1
    rw [atBlock_call blocks 1#usize (by decide)]
    simp only [bind_tc_ok]
    rw [src1,own1]
    simp only [bind_tc_ok]
    cases stop1 with
    | true =>
      dsimp only
      simp only [if_true]
      exact finish_source s1 advances 1#usize (by decide)
    | false =>
      dsimp only
      simp only [Bool.false_eq_true,if_false]
      obtain ⟨s2,next2,stop2,own2,v2,src2,sel2⟩ :=
        step_source s1 (atBlock advances 7#usize (by decide)) 2#usize blocks advances (by decide) v1
      rw [sel2] at own2
      rw [atBlock_call blocks 2#usize (by decide)]
      simp only [bind_tc_ok]
      rw [src2,own2]
      simp only [bind_tc_ok]
      cases stop2 with
      | true =>
        dsimp only
        simp only [if_true]
        exact finish_source s2 advances 2#usize (by decide)
      | false =>
        dsimp only
        simp only [Bool.false_eq_true,if_false]
        obtain ⟨s3,next3,stop3,own3,v3,src3,sel3⟩ :=
          step_source s2 (atBlock advances 7#usize (by decide)) 3#usize blocks advances (by decide) v2
        rw [sel3] at own3
        rw [atBlock_call blocks 3#usize (by decide)]
        simp only [bind_tc_ok]
        rw [src3,own3]
        simp only [bind_tc_ok]
        cases stop3 with
        | true =>
          dsimp only
          simp only [if_true]
          exact finish_source s3 advances 3#usize (by decide)
        | false =>
          dsimp only
          simp only [Bool.false_eq_true,if_false]
          obtain ⟨s4,next4,stop4,own4,v4,src4,sel4⟩ :=
            step_source s3 (atBlock advances 7#usize (by decide)) 4#usize blocks advances (by decide) v3
          rw [sel4] at own4
          rw [atBlock_call blocks 4#usize (by decide)]
          simp only [bind_tc_ok]
          rw [src4,own4]
          simp only [bind_tc_ok]
          cases stop4 with
          | true =>
            dsimp only
            simp only [if_true]
            exact finish_source s4 advances 4#usize (by decide)
          | false =>
            dsimp only
            simp only [Bool.false_eq_true,if_false]
            obtain ⟨s5,next5,stop5,own5,v5,src5,sel5⟩ :=
              step_source s4 (atBlock advances 7#usize (by decide)) 5#usize blocks advances (by decide) v4
            rw [sel5] at own5
            rw [atBlock_call blocks 5#usize (by decide)]
            simp only [bind_tc_ok]
            rw [src5,own5]
            simp only [bind_tc_ok]
            cases stop5 with
            | true =>
              dsimp only
              simp only [if_true]
              exact finish_source s5 advances 5#usize (by decide)
            | false =>
              dsimp only
              simp only [Bool.false_eq_true,if_false]
              obtain ⟨s6,next6,stop6,own6,v6,src6,sel6⟩ :=
                step_source s5 (atBlock advances 7#usize (by decide)) 6#usize blocks advances (by decide) v5
              rw [sel6] at own6
              rw [atBlock_call blocks 6#usize (by decide)]
              simp only [bind_tc_ok]
              rw [src6,own6]
              simp only [bind_tc_ok]
              cases stop6 with
              | true =>
                dsimp only
                simp only [if_true]
                exact finish_source s6 advances 6#usize (by decide)
              | false =>
                dsimp only
                simp only [Bool.false_eq_true,if_false]
                obtain ⟨s7,next7,stop7,own7,v7,src7,sel7⟩ :=
                  step_source s6 (atBlock advances 7#usize (by decide)) 7#usize blocks advances (by decide) v6
                rw [sel7] at own7
                rw [atBlock_call blocks 7#usize (by decide)]
                simp only [bind_tc_ok]
                rw [src7,own7]
                simp only [bind_tc_ok]
                cases stop7 with
                | true =>
                  dsimp only
                  simp only [if_true]
                  exact finish_source s7 advances 7#usize (by decide)
                | false =>
                  dsimp only
                  simp only [Bool.false_eq_true,if_false]
                  exact finish_source s7 advances 7#usize (by decide)

#print axioms reference_eq_source
end AspisS1OwnedQueryPairs.Model
