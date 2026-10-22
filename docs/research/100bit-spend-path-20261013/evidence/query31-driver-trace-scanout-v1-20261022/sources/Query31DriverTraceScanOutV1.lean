import S4ScanOutRunCoreV1
import QueryFinishAcceptedBridgeV1
import Query31ModelScanCall
import Query31ConcreteDriverTraceFacts
import Query31ConcreteWordsDriverChain
import QueryWordsSamplerBridgeV1
import RawDigestLogCarrier
import AspisV8R19.DuplexFrames

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1Query31DriverTraceScanOutV1
open AspisV8R19.Q22WordScan AspisV8R19.SourceDuplexStep AspisV8R19.SamplerWords
open AspisV8R19.SqueezeOracleBridge
open Query31ExplicitListLoop Query31ExplicitScanBody Query31ModelScanCall
open Query31ConcreteDriverTraceFacts Query31ModelDriverChain
open AspisR1Query31Transcript
open AspisR1.S4ScanOutRunCoreV1

abbrev QScan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan
abbrev Bytes32 := Array Std.U8 32#usize
abbrev QueryOutput := Array Std.U32 22#usize

private theorem index_value_of_ok {A : Type}
    (xs : Array A 8#usize) (i : Usize) (x : A)
    (hi : i.val < 8)
    (h : Array.index_usize xs i = .ok x) :
    xs.val[i.val]'(by simpa [xs.property] using hi) = x := by
  have hlen : i.val < xs.length := by simpa [xs.property] using hi
  obtain ⟨v,hv,hget⟩ := WP.spec_imp_exists (Array.index_usize_spec xs i hlen)
  have heq : v = x := Result.ok.inj (hv.symm.trans h)
  have hx := heq.symm.trans hget
  exact hx.symm

private theorem index_ok {A : Type}
    (xs : Array A 8#usize) (i : Usize) (hi : i.val < 8) :
    Array.index_usize xs i = .ok (xs.val[i.val]'(by simpa [xs.property] using hi)) := by
  have hidx : i.val < xs.val.length := by simpa [xs.property] using hi
  unfold Array.index_usize
  change (match xs.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (xs.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem map_drop_of_index {A B : Type}
    (xs : Array A 8#usize) (i : Usize) (hi : i.val < 8)
    (f : A → B) (x : A)
    (h : Array.index_usize xs i = .ok x) :
    (xs.val.map f).drop i.val = f x :: (xs.val.map f).drop (i.val + 1) := by
  have hlen : i.val < (xs.val.map f).length := by
    simp [xs.property]
    exact hi
  have hv := index_value_of_ok xs i x hi h
  rw [List.drop_eq_getElem_cons hlen]
  simp only [List.getElem_map]
  rw [hv]

private theorem false_scan_draws_add_eight
    (q q' : ScanState) (b : State)
    (hscan : scan q (words 18 b) = (q',false)) : q'.draws = q.draws + 8 := by
  have hfalse : (scan q (words 18 b)).2 = false := by rw [hscan]
  have hp := AspisV8R19.Q22WordScan.scan_progress q (words 18 b) hfalse
  have hfirst : (scan q (words 18 b)).1 = q' := by rw [hscan]
  rw [hfirst, AspisV8R19.SamplerWords.words_length] at hp
  exact hp

private theorem actual_step_semantic_valid
    (s s' : QScan) (b : Bytes32) (stop : Bool)
    (hvalid : Query31ExplicitListLoop.validState s)
    (hcall : Query31ModelScanCall.modelScanFn
      Query31ConcreteWordsDriverChain.actualQueryWords s b = .ok (stop,s')) :
    scan (Query31ExplicitScanBody.q22StateOf s)
      (words 18 (AspisR1DigestLogCarrier.decodeState b)) =
        (Query31ExplicitScanBody.q22StateOf s', stop) ∧
      Query31ExplicitListLoop.validState s' := by
  obtain ⟨w, hdecode, hscan, hvalid'⟩ :=
    Query31ModelScanCall.modelScanFn_success
      Query31ConcreteWordsDriverChain.actualQueryWords s s' b stop hvalid hcall
  have hwords := AspisR1QueryWordsSamplerBridgeV1.query_words_success_sampler_words18 b w hdecode
  rw [hwords] at hscan
  exact ⟨hscan, hvalid'⟩

private theorem source_finish_q22
    (s : QScan) (accepted : QueryOutput)
    (hfinish : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s =
      .ok (.Ok accepted)) :
    AspisV8R19.Q22WordScan.finish (Query31ExplicitScanBody.q22StateOf s) =
      .ok (accepted.val.map (fun w => w.val)) := by
  have hsource := (AspisR1Query31Transcript.finish_success_iff s accepted).mp hfinish
  have hcountval : s.accepted_len.val = 22 := by
    have h := congrArg UScalar.val hsource.1
    have hq : AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT.val = 22 := by
      unfold AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT
      scalar_tac
    simpa [hq] using h
  have harray : s.accepted.val.length = 22 := by
    have h := s.accepted.property
    scalar_tac
  have hprefix : s.accepted.val.take s.accepted_len.val = s.accepted.val := by
    rw [hcountval]
    apply List.take_of_length_le
    rw [harray]
  have hlen : (Query31ExplicitScanBody.q22StateOf s).accepted.length = 22 := by
    change ((s.accepted.val.take s.accepted_len.val).map (fun w => w.val)).length = 22
    simp only [List.length_map]
    rw [hprefix, harray]
  have hmap := AspisR1QueryFinishAcceptedBridgeV1.finish_success_accepted_values s accepted hfinish
  unfold AspisV8R19.Q22WordScan.finish
  rw [if_pos hlen]
  exact congrArg Except.ok hmap.symm

/-- The exact full-array scanOut result from the unrolled generated query driver.
The oracle fallback `initial` remains arbitrary; every successful source trace
starts from an empty Q22 draw counter so the eight model guards are reached. -/
theorem successful_driver_trace_scanOut
    (blocks advances : Array Bytes32 8#usize)
    (s0 : QScan) (accepted : QueryOutput) (next : Bytes32)
    (initial : AspisV8R19.SourceDuplexStep.State)
    (hvalid0 : Query31ExplicitListLoop.validState s0)
    (hdraw0 : (Query31ExplicitScanBody.q22StateOf s0).draws = 0)
    (htrace : AspisR1Query31Transcript.DriverTrace
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      blocks advances s0 accepted next) :
    R0C.V3.Q22.scanOut 8 (Query31ExplicitScanBody.q22StateOf s0)
      (blocks.val.map AspisR1DigestLogCarrier.decodeState)
      (advances.val.map AspisR1DigestLogCarrier.decodeState) initial =
      (.ok (accepted.val.map (fun w => w.val)),
        AspisR1DigestLogCarrier.decodeState next) := by
  cases htrace with
  | stop0 b0 s1 hblock0 hscan0 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 true hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s1) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState next :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      exact Run.stopped hg0 hs0
    have hfinishQ := source_finish_q22 s1 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 true hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s2) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      exact Run.stopped hg1 hs1
    have hfinishQ := source_finish_q22 s2 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 true hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s3) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      exact Run.stopped hg2 hs2
    have hfinishQ := source_finish_q22 s3 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 false hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hp3 := actual_step_semantic_valid s3 s4 b3 true hv3 hscan3
    have hs3 := hp3.1
    have hv4 := hp3.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hd3 : (Query31ExplicitScanBody.q22StateOf s3).draws = 24 := by
      have hp := false_scan_draws_add_eight _ _ _ hs2
      rw [hd2] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hg3 : (Query31ExplicitScanBody.q22StateOf s3).draws < 64 := by
      rw [hd3]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hb3 : bs.drop 3 = AspisR1DigestLogCarrier.decodeState b3 :: bs.drop 4 := by
      simpa [bs] using map_drop_of_index blocks (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b3 hblock3
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hxidx2 := index_ok advances (2#usize) (by scalar_tac)
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState (advances.val[2]'(by scalar_tac)) :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx2
    have hx3 : xs.drop 3 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 4 := by
      simpa [xs] using map_drop_of_index advances (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s4) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      refine Run.continued hg2 hs2 ?_
      rw [hb3, hx3]
      exact Run.stopped hg3 hs3
    have hfinishQ := source_finish_q22 s4 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 false hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hp3 := actual_step_semantic_valid s3 s4 b3 false hv3 hscan3
    have hs3 := hp3.1
    have hv4 := hp3.2
    have hp4 := actual_step_semantic_valid s4 s5 b4 true hv4 hscan4
    have hs4 := hp4.1
    have hv5 := hp4.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hd3 : (Query31ExplicitScanBody.q22StateOf s3).draws = 24 := by
      have hp := false_scan_draws_add_eight _ _ _ hs2
      rw [hd2] at hp
      omega
    have hd4 : (Query31ExplicitScanBody.q22StateOf s4).draws = 32 := by
      have hp := false_scan_draws_add_eight _ _ _ hs3
      rw [hd3] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hg3 : (Query31ExplicitScanBody.q22StateOf s3).draws < 64 := by
      rw [hd3]
      omega
    have hg4 : (Query31ExplicitScanBody.q22StateOf s4).draws < 64 := by
      rw [hd4]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hb3 : bs.drop 3 = AspisR1DigestLogCarrier.decodeState b3 :: bs.drop 4 := by
      simpa [bs] using map_drop_of_index blocks (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b3 hblock3
    have hb4 : bs.drop 4 = AspisR1DigestLogCarrier.decodeState b4 :: bs.drop 5 := by
      simpa [bs] using map_drop_of_index blocks (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b4 hblock4
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hxidx2 := index_ok advances (2#usize) (by scalar_tac)
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState (advances.val[2]'(by scalar_tac)) :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx2
    have hxidx3 := index_ok advances (3#usize) (by scalar_tac)
    have hx3 : xs.drop 3 = AspisR1DigestLogCarrier.decodeState (advances.val[3]'(by scalar_tac)) :: xs.drop 4 := by
      simpa [xs] using map_drop_of_index advances (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx3
    have hx4 : xs.drop 4 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 5 := by
      simpa [xs] using map_drop_of_index advances (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s5) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      refine Run.continued hg2 hs2 ?_
      rw [hb3, hx3]
      refine Run.continued hg3 hs3 ?_
      rw [hb4, hx4]
      exact Run.stopped hg4 hs4
    have hfinishQ := source_finish_q22 s5 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 false hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hp3 := actual_step_semantic_valid s3 s4 b3 false hv3 hscan3
    have hs3 := hp3.1
    have hv4 := hp3.2
    have hp4 := actual_step_semantic_valid s4 s5 b4 false hv4 hscan4
    have hs4 := hp4.1
    have hv5 := hp4.2
    have hp5 := actual_step_semantic_valid s5 s6 b5 true hv5 hscan5
    have hs5 := hp5.1
    have hv6 := hp5.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hd3 : (Query31ExplicitScanBody.q22StateOf s3).draws = 24 := by
      have hp := false_scan_draws_add_eight _ _ _ hs2
      rw [hd2] at hp
      omega
    have hd4 : (Query31ExplicitScanBody.q22StateOf s4).draws = 32 := by
      have hp := false_scan_draws_add_eight _ _ _ hs3
      rw [hd3] at hp
      omega
    have hd5 : (Query31ExplicitScanBody.q22StateOf s5).draws = 40 := by
      have hp := false_scan_draws_add_eight _ _ _ hs4
      rw [hd4] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hg3 : (Query31ExplicitScanBody.q22StateOf s3).draws < 64 := by
      rw [hd3]
      omega
    have hg4 : (Query31ExplicitScanBody.q22StateOf s4).draws < 64 := by
      rw [hd4]
      omega
    have hg5 : (Query31ExplicitScanBody.q22StateOf s5).draws < 64 := by
      rw [hd5]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hb3 : bs.drop 3 = AspisR1DigestLogCarrier.decodeState b3 :: bs.drop 4 := by
      simpa [bs] using map_drop_of_index blocks (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b3 hblock3
    have hb4 : bs.drop 4 = AspisR1DigestLogCarrier.decodeState b4 :: bs.drop 5 := by
      simpa [bs] using map_drop_of_index blocks (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b4 hblock4
    have hb5 : bs.drop 5 = AspisR1DigestLogCarrier.decodeState b5 :: bs.drop 6 := by
      simpa [bs] using map_drop_of_index blocks (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b5 hblock5
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hxidx2 := index_ok advances (2#usize) (by scalar_tac)
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState (advances.val[2]'(by scalar_tac)) :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx2
    have hxidx3 := index_ok advances (3#usize) (by scalar_tac)
    have hx3 : xs.drop 3 = AspisR1DigestLogCarrier.decodeState (advances.val[3]'(by scalar_tac)) :: xs.drop 4 := by
      simpa [xs] using map_drop_of_index advances (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx3
    have hxidx4 := index_ok advances (4#usize) (by scalar_tac)
    have hx4 : xs.drop 4 = AspisR1DigestLogCarrier.decodeState (advances.val[4]'(by scalar_tac)) :: xs.drop 5 := by
      simpa [xs] using map_drop_of_index advances (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx4
    have hx5 : xs.drop 5 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 6 := by
      simpa [xs] using map_drop_of_index advances (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s6) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      refine Run.continued hg2 hs2 ?_
      rw [hb3, hx3]
      refine Run.continued hg3 hs3 ?_
      rw [hb4, hx4]
      refine Run.continued hg4 hs4 ?_
      rw [hb5, hx5]
      exact Run.stopped hg5 hs5
    have hfinishQ := source_finish_q22 s6 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 false hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hp3 := actual_step_semantic_valid s3 s4 b3 false hv3 hscan3
    have hs3 := hp3.1
    have hv4 := hp3.2
    have hp4 := actual_step_semantic_valid s4 s5 b4 false hv4 hscan4
    have hs4 := hp4.1
    have hv5 := hp4.2
    have hp5 := actual_step_semantic_valid s5 s6 b5 false hv5 hscan5
    have hs5 := hp5.1
    have hv6 := hp5.2
    have hp6 := actual_step_semantic_valid s6 s7 b6 true hv6 hscan6
    have hs6 := hp6.1
    have hv7 := hp6.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hd3 : (Query31ExplicitScanBody.q22StateOf s3).draws = 24 := by
      have hp := false_scan_draws_add_eight _ _ _ hs2
      rw [hd2] at hp
      omega
    have hd4 : (Query31ExplicitScanBody.q22StateOf s4).draws = 32 := by
      have hp := false_scan_draws_add_eight _ _ _ hs3
      rw [hd3] at hp
      omega
    have hd5 : (Query31ExplicitScanBody.q22StateOf s5).draws = 40 := by
      have hp := false_scan_draws_add_eight _ _ _ hs4
      rw [hd4] at hp
      omega
    have hd6 : (Query31ExplicitScanBody.q22StateOf s6).draws = 48 := by
      have hp := false_scan_draws_add_eight _ _ _ hs5
      rw [hd5] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hg3 : (Query31ExplicitScanBody.q22StateOf s3).draws < 64 := by
      rw [hd3]
      omega
    have hg4 : (Query31ExplicitScanBody.q22StateOf s4).draws < 64 := by
      rw [hd4]
      omega
    have hg5 : (Query31ExplicitScanBody.q22StateOf s5).draws < 64 := by
      rw [hd5]
      omega
    have hg6 : (Query31ExplicitScanBody.q22StateOf s6).draws < 64 := by
      rw [hd6]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hb3 : bs.drop 3 = AspisR1DigestLogCarrier.decodeState b3 :: bs.drop 4 := by
      simpa [bs] using map_drop_of_index blocks (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b3 hblock3
    have hb4 : bs.drop 4 = AspisR1DigestLogCarrier.decodeState b4 :: bs.drop 5 := by
      simpa [bs] using map_drop_of_index blocks (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b4 hblock4
    have hb5 : bs.drop 5 = AspisR1DigestLogCarrier.decodeState b5 :: bs.drop 6 := by
      simpa [bs] using map_drop_of_index blocks (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b5 hblock5
    have hb6 : bs.drop 6 = AspisR1DigestLogCarrier.decodeState b6 :: bs.drop 7 := by
      simpa [bs] using map_drop_of_index blocks (6#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b6 hblock6
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hxidx2 := index_ok advances (2#usize) (by scalar_tac)
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState (advances.val[2]'(by scalar_tac)) :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx2
    have hxidx3 := index_ok advances (3#usize) (by scalar_tac)
    have hx3 : xs.drop 3 = AspisR1DigestLogCarrier.decodeState (advances.val[3]'(by scalar_tac)) :: xs.drop 4 := by
      simpa [xs] using map_drop_of_index advances (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx3
    have hxidx4 := index_ok advances (4#usize) (by scalar_tac)
    have hx4 : xs.drop 4 = AspisR1DigestLogCarrier.decodeState (advances.val[4]'(by scalar_tac)) :: xs.drop 5 := by
      simpa [xs] using map_drop_of_index advances (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx4
    have hxidx5 := index_ok advances (5#usize) (by scalar_tac)
    have hx5 : xs.drop 5 = AspisR1DigestLogCarrier.decodeState (advances.val[5]'(by scalar_tac)) :: xs.drop 6 := by
      simpa [xs] using map_drop_of_index advances (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx5
    have hx6 : xs.drop 6 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 7 := by
      simpa [xs] using map_drop_of_index advances (6#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s7) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      refine Run.continued hg2 hs2 ?_
      rw [hb3, hx3]
      refine Run.continued hg3 hs3 ?_
      rw [hb4, hx4]
      refine Run.continued hg4 hs4 ?_
      rw [hb5, hx5]
      refine Run.continued hg5 hs5 ?_
      rw [hb6, hx6]
      exact Run.stopped hg6 hs6
    have hfinishQ := source_finish_q22 s7 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]
  | stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 lastStop hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hfinish hadvance =>
    let bs := blocks.val.map AspisR1DigestLogCarrier.decodeState
    let xs := advances.val.map AspisR1DigestLogCarrier.decodeState
    have hp0 := actual_step_semantic_valid s0 s1 b0 false hvalid0 hscan0
    have hs0 := hp0.1
    have hv1 := hp0.2
    have hp1 := actual_step_semantic_valid s1 s2 b1 false hv1 hscan1
    have hs1 := hp1.1
    have hv2 := hp1.2
    have hp2 := actual_step_semantic_valid s2 s3 b2 false hv2 hscan2
    have hs2 := hp2.1
    have hv3 := hp2.2
    have hp3 := actual_step_semantic_valid s3 s4 b3 false hv3 hscan3
    have hs3 := hp3.1
    have hv4 := hp3.2
    have hp4 := actual_step_semantic_valid s4 s5 b4 false hv4 hscan4
    have hs4 := hp4.1
    have hv5 := hp4.2
    have hp5 := actual_step_semantic_valid s5 s6 b5 false hv5 hscan5
    have hs5 := hp5.1
    have hv6 := hp5.2
    have hp6 := actual_step_semantic_valid s6 s7 b6 false hv6 hscan6
    have hs6 := hp6.1
    have hv7 := hp6.2
    have hp7 := actual_step_semantic_valid s7 s8 b7 lastStop hv7 hscan7
    have hs7 := hp7.1
    have hv8 := hp7.2
    have hd1 : (Query31ExplicitScanBody.q22StateOf s1).draws = 8 := by
      have hp := false_scan_draws_add_eight _ _ _ hs0
      rw [hdraw0] at hp
      omega
    have hd2 : (Query31ExplicitScanBody.q22StateOf s2).draws = 16 := by
      have hp := false_scan_draws_add_eight _ _ _ hs1
      rw [hd1] at hp
      omega
    have hd3 : (Query31ExplicitScanBody.q22StateOf s3).draws = 24 := by
      have hp := false_scan_draws_add_eight _ _ _ hs2
      rw [hd2] at hp
      omega
    have hd4 : (Query31ExplicitScanBody.q22StateOf s4).draws = 32 := by
      have hp := false_scan_draws_add_eight _ _ _ hs3
      rw [hd3] at hp
      omega
    have hd5 : (Query31ExplicitScanBody.q22StateOf s5).draws = 40 := by
      have hp := false_scan_draws_add_eight _ _ _ hs4
      rw [hd4] at hp
      omega
    have hd6 : (Query31ExplicitScanBody.q22StateOf s6).draws = 48 := by
      have hp := false_scan_draws_add_eight _ _ _ hs5
      rw [hd5] at hp
      omega
    have hd7 : (Query31ExplicitScanBody.q22StateOf s7).draws = 56 := by
      have hp := false_scan_draws_add_eight _ _ _ hs6
      rw [hd6] at hp
      omega
    have hg0 : (Query31ExplicitScanBody.q22StateOf s0).draws < 64 := by
      rw [hdraw0]
      omega
    have hg1 : (Query31ExplicitScanBody.q22StateOf s1).draws < 64 := by
      rw [hd1]
      omega
    have hg2 : (Query31ExplicitScanBody.q22StateOf s2).draws < 64 := by
      rw [hd2]
      omega
    have hg3 : (Query31ExplicitScanBody.q22StateOf s3).draws < 64 := by
      rw [hd3]
      omega
    have hg4 : (Query31ExplicitScanBody.q22StateOf s4).draws < 64 := by
      rw [hd4]
      omega
    have hg5 : (Query31ExplicitScanBody.q22StateOf s5).draws < 64 := by
      rw [hd5]
      omega
    have hg6 : (Query31ExplicitScanBody.q22StateOf s6).draws < 64 := by
      rw [hd6]
      omega
    have hg7 : (Query31ExplicitScanBody.q22StateOf s7).draws < 64 := by
      rw [hd7]
      omega
    have hb0 : bs.drop 0 = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
      simpa [bs] using map_drop_of_index blocks (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b0 hblock0
    have hb1 : bs.drop 1 = AspisR1DigestLogCarrier.decodeState b1 :: bs.drop 2 := by
      simpa [bs] using map_drop_of_index blocks (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b1 hblock1
    have hb2 : bs.drop 2 = AspisR1DigestLogCarrier.decodeState b2 :: bs.drop 3 := by
      simpa [bs] using map_drop_of_index blocks (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b2 hblock2
    have hb3 : bs.drop 3 = AspisR1DigestLogCarrier.decodeState b3 :: bs.drop 4 := by
      simpa [bs] using map_drop_of_index blocks (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b3 hblock3
    have hb4 : bs.drop 4 = AspisR1DigestLogCarrier.decodeState b4 :: bs.drop 5 := by
      simpa [bs] using map_drop_of_index blocks (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b4 hblock4
    have hb5 : bs.drop 5 = AspisR1DigestLogCarrier.decodeState b5 :: bs.drop 6 := by
      simpa [bs] using map_drop_of_index blocks (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b5 hblock5
    have hb6 : bs.drop 6 = AspisR1DigestLogCarrier.decodeState b6 :: bs.drop 7 := by
      simpa [bs] using map_drop_of_index blocks (6#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b6 hblock6
    have hb7 : bs.drop 7 = AspisR1DigestLogCarrier.decodeState b7 :: bs.drop 8 := by
      simpa [bs] using map_drop_of_index blocks (7#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState b7 hblock7
    have hxidx0 := index_ok advances (0#usize) (by scalar_tac)
    have hx0 : xs.drop 0 = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
      simpa [xs] using map_drop_of_index advances (0#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx0
    have hxidx1 := index_ok advances (1#usize) (by scalar_tac)
    have hx1 : xs.drop 1 = AspisR1DigestLogCarrier.decodeState (advances.val[1]'(by scalar_tac)) :: xs.drop 2 := by
      simpa [xs] using map_drop_of_index advances (1#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx1
    have hxidx2 := index_ok advances (2#usize) (by scalar_tac)
    have hx2 : xs.drop 2 = AspisR1DigestLogCarrier.decodeState (advances.val[2]'(by scalar_tac)) :: xs.drop 3 := by
      simpa [xs] using map_drop_of_index advances (2#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx2
    have hxidx3 := index_ok advances (3#usize) (by scalar_tac)
    have hx3 : xs.drop 3 = AspisR1DigestLogCarrier.decodeState (advances.val[3]'(by scalar_tac)) :: xs.drop 4 := by
      simpa [xs] using map_drop_of_index advances (3#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx3
    have hxidx4 := index_ok advances (4#usize) (by scalar_tac)
    have hx4 : xs.drop 4 = AspisR1DigestLogCarrier.decodeState (advances.val[4]'(by scalar_tac)) :: xs.drop 5 := by
      simpa [xs] using map_drop_of_index advances (4#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx4
    have hxidx5 := index_ok advances (5#usize) (by scalar_tac)
    have hx5 : xs.drop 5 = AspisR1DigestLogCarrier.decodeState (advances.val[5]'(by scalar_tac)) :: xs.drop 6 := by
      simpa [xs] using map_drop_of_index advances (5#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx5
    have hxidx6 := index_ok advances (6#usize) (by scalar_tac)
    have hx6 : xs.drop 6 = AspisR1DigestLogCarrier.decodeState (advances.val[6]'(by scalar_tac)) :: xs.drop 7 := by
      simpa [xs] using map_drop_of_index advances (6#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState _ hxidx6
    have hx7 : xs.drop 7 = AspisR1DigestLogCarrier.decodeState next :: xs.drop 8 := by
      simpa [xs] using map_drop_of_index advances (7#usize) (by scalar_tac) AspisR1DigestLogCarrier.decodeState next hadvance
    have hrun : Run 8 (Query31ExplicitScanBody.q22StateOf s0) bs xs
        (Query31ExplicitScanBody.q22StateOf s8) initial
        (AspisR1DigestLogCarrier.decodeState next) := by
      have hbs0 : bs = AspisR1DigestLogCarrier.decodeState b0 :: bs.drop 1 := by
        simpa using hb0
      have hxs0 : xs = AspisR1DigestLogCarrier.decodeState (advances.val[0]'(by scalar_tac)) :: xs.drop 1 := by
        simpa using hx0
      rw [hbs0, hxs0]
      refine Run.continued hg0 hs0 ?_
      rw [hb1, hx1]
      refine Run.continued hg1 hs1 ?_
      rw [hb2, hx2]
      refine Run.continued hg2 hs2 ?_
      rw [hb3, hx3]
      refine Run.continued hg3 hs3 ?_
      rw [hb4, hx4]
      refine Run.continued hg4 hs4 ?_
      rw [hb5, hx5]
      refine Run.continued hg5 hs5 ?_
      rw [hb6, hx6]
      refine Run.continued hg6 hs6 ?_
      rw [hb7, hx7]
      cases lastStop with
      | true => exact Run.stopped hg7 hs7
      | false =>
          have hbtail : bs.drop 8 = [] := by simp [bs, blocks.property]
          have hxtail : xs.drop 8 = [] := by simp [xs, advances.property]
          rw [hbtail, hxtail]
          refine Run.continued hg7 hs7 ?_
          exact Run.done _ (AspisR1DigestLogCarrier.decodeState next)
    have hfinishQ := source_finish_q22 s8 accepted hfinish
    rw [scanOut_of_run hrun, hfinishQ]

#print axioms successful_driver_trace_scanOut
end AspisR1Query31DriverTraceScanOutV1
