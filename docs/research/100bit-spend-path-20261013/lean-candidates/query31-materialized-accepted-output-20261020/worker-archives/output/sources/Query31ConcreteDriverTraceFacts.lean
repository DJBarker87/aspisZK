import Query31ModelDriverChain
import Query31UnrolledDriverFirstStop
import Query31ExplicitListLoop
import Query31ExplicitScanBody
import Query31ModelScanCall
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ExplicitListLoop Query31ExplicitScanBody Query31ModelScanCall
open Query31ModelDriverChain
set_option autoImplicit false
noncomputable section

namespace Query31ConcreteDriverTraceFacts

abbrev QueryScan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan

/-- Exact source-shaped value returned by QueryScan::default: the fixed-size
    DefaultArray is all zero and both Usize counters are zero. -/
def sourceDefaultState : QueryScan :=
  { accepted := ⟨List.replicate 22 (0#u32), by simp⟩
    accepted_len := 0#usize
    draws := 0#usize }

theorem sourceDefaultState_maps_to_empty_q22 :
    Query31ExplicitScanBody.q22StateOf sourceDefaultState = ⟨[], 0⟩ := by
  simp [sourceDefaultState, Query31ExplicitScanBody.q22StateOf,
    Query31ExplicitScanBody.acceptedPrefix]

theorem sourceDefaultState_valid :
    Query31ExplicitListLoop.validState sourceDefaultState := by
  apply Query31ExplicitListLoop.validState_of_bounds
  · simp [sourceDefaultState]
  · simp [sourceDefaultState]

theorem driver_trace_q22_chain_with_finish
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : QueryScan) (accepted : Array Std.U32 22#usize)
    (next : Array Std.U8 32#usize)
    (hstart : validState s0)
    (htrace : AspisR1Query31Transcript.DriverTrace
      (modelScanFn decodeBlock) blocks advances s0 accepted next) :
    ∃ evidence sf stopIndex,
      Q22ScanChain decodeBlock blocks s0 evidence sf ∧
      evidence.length ≤ 8 ∧ validState sf ∧
      AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish sf =
        .ok (.Ok accepted) ∧
      sf.accepted_len = AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT ∧
      sf.accepted = accepted ∧
      Array.index_usize advances stopIndex = .ok next ∧ stopIndex.val ≤ 7 := by
  cases htrace with
  | stop0 b0 s1 hblock0 hscan0 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s1 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 true hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := true, selected := hblock0, decode_ok := hd0 }
    refine ⟨e0 :: [], s1, 0#usize, ?_, by simp, hv1, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.nil s1 hv1)
  | stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s2 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 true hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := true, selected := hblock1, decode_ok := hd1 }
    refine ⟨e0 :: e1 :: [], s2, 1#usize, ?_, by simp, hv2, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.nil s2 hv2))
  | stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s3 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 true hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := true, selected := hblock2, decode_ok := hd2 }
    refine ⟨e0 :: e1 :: e2 :: [], s3, 2#usize, ?_, by simp, hv3, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.nil s3 hv3)))
  | stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s4 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 false hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := false, selected := hblock2, decode_ok := hd2 }
    obtain ⟨w3, hd3, hq3, hv4⟩ :=
      modelScanFn_success decodeBlock s3 s4 b3 true hv3 hscan3
    let e3 : BlockEvidence decodeBlock blocks :=
      { index := 3#usize, bytes := b3, words := w3, stop := true, selected := hblock3, decode_ok := hd3 }
    refine ⟨e0 :: e1 :: e2 :: e3 :: [], s4, 3#usize, ?_, by simp, hv4, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.nil s4 hv4))))
  | stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s5 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 false hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := false, selected := hblock2, decode_ok := hd2 }
    obtain ⟨w3, hd3, hq3, hv4⟩ :=
      modelScanFn_success decodeBlock s3 s4 b3 false hv3 hscan3
    let e3 : BlockEvidence decodeBlock blocks :=
      { index := 3#usize, bytes := b3, words := w3, stop := false, selected := hblock3, decode_ok := hd3 }
    obtain ⟨w4, hd4, hq4, hv5⟩ :=
      modelScanFn_success decodeBlock s4 s5 b4 true hv4 hscan4
    let e4 : BlockEvidence decodeBlock blocks :=
      { index := 4#usize, bytes := b4, words := w4, stop := true, selected := hblock4, decode_ok := hd4 }
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: [], s5, 4#usize, ?_, by simp, hv5, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.nil s5 hv5)))))
  | stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s6 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 false hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := false, selected := hblock2, decode_ok := hd2 }
    obtain ⟨w3, hd3, hq3, hv4⟩ :=
      modelScanFn_success decodeBlock s3 s4 b3 false hv3 hscan3
    let e3 : BlockEvidence decodeBlock blocks :=
      { index := 3#usize, bytes := b3, words := w3, stop := false, selected := hblock3, decode_ok := hd3 }
    obtain ⟨w4, hd4, hq4, hv5⟩ :=
      modelScanFn_success decodeBlock s4 s5 b4 false hv4 hscan4
    let e4 : BlockEvidence decodeBlock blocks :=
      { index := 4#usize, bytes := b4, words := w4, stop := false, selected := hblock4, decode_ok := hd4 }
    obtain ⟨w5, hd5, hq5, hv6⟩ :=
      modelScanFn_success decodeBlock s5 s6 b5 true hv5 hscan5
    let e5 : BlockEvidence decodeBlock blocks :=
      { index := 5#usize, bytes := b5, words := w5, stop := true, selected := hblock5, decode_ok := hd5 }
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: [], s6, 5#usize, ?_, by simp, hv6, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.nil s6 hv6))))))
  | stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s7 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 false hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := false, selected := hblock2, decode_ok := hd2 }
    obtain ⟨w3, hd3, hq3, hv4⟩ :=
      modelScanFn_success decodeBlock s3 s4 b3 false hv3 hscan3
    let e3 : BlockEvidence decodeBlock blocks :=
      { index := 3#usize, bytes := b3, words := w3, stop := false, selected := hblock3, decode_ok := hd3 }
    obtain ⟨w4, hd4, hq4, hv5⟩ :=
      modelScanFn_success decodeBlock s4 s5 b4 false hv4 hscan4
    let e4 : BlockEvidence decodeBlock blocks :=
      { index := 4#usize, bytes := b4, words := w4, stop := false, selected := hblock4, decode_ok := hd4 }
    obtain ⟨w5, hd5, hq5, hv6⟩ :=
      modelScanFn_success decodeBlock s5 s6 b5 false hv5 hscan5
    let e5 : BlockEvidence decodeBlock blocks :=
      { index := 5#usize, bytes := b5, words := w5, stop := false, selected := hblock5, decode_ok := hd5 }
    obtain ⟨w6, hd6, hq6, hv7⟩ :=
      modelScanFn_success decodeBlock s6 s7 b6 true hv6 hscan6
    let e6 : BlockEvidence decodeBlock blocks :=
      { index := 6#usize, bytes := b6, words := w6, stop := true, selected := hblock6, decode_ok := hd6 }
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: [], s7, 6#usize, ?_, by simp, hv7, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.cons hv6 hscan6 hq6 hv7 (Q22ScanChain.nil s7 hv7)))))))
  | stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 lastStop hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hfinish hadvance =>
    have hfacts := (AspisR1Query31Transcript.finish_success_iff s8 accepted).mp hfinish
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 false hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := false, selected := hblock1, decode_ok := hd1 }
    obtain ⟨w2, hd2, hq2, hv3⟩ :=
      modelScanFn_success decodeBlock s2 s3 b2 false hv2 hscan2
    let e2 : BlockEvidence decodeBlock blocks :=
      { index := 2#usize, bytes := b2, words := w2, stop := false, selected := hblock2, decode_ok := hd2 }
    obtain ⟨w3, hd3, hq3, hv4⟩ :=
      modelScanFn_success decodeBlock s3 s4 b3 false hv3 hscan3
    let e3 : BlockEvidence decodeBlock blocks :=
      { index := 3#usize, bytes := b3, words := w3, stop := false, selected := hblock3, decode_ok := hd3 }
    obtain ⟨w4, hd4, hq4, hv5⟩ :=
      modelScanFn_success decodeBlock s4 s5 b4 false hv4 hscan4
    let e4 : BlockEvidence decodeBlock blocks :=
      { index := 4#usize, bytes := b4, words := w4, stop := false, selected := hblock4, decode_ok := hd4 }
    obtain ⟨w5, hd5, hq5, hv6⟩ :=
      modelScanFn_success decodeBlock s5 s6 b5 false hv5 hscan5
    let e5 : BlockEvidence decodeBlock blocks :=
      { index := 5#usize, bytes := b5, words := w5, stop := false, selected := hblock5, decode_ok := hd5 }
    obtain ⟨w6, hd6, hq6, hv7⟩ :=
      modelScanFn_success decodeBlock s6 s7 b6 false hv6 hscan6
    let e6 : BlockEvidence decodeBlock blocks :=
      { index := 6#usize, bytes := b6, words := w6, stop := false, selected := hblock6, decode_ok := hd6 }
    obtain ⟨w7, hd7, hq7, hv8⟩ :=
      modelScanFn_success decodeBlock s7 s8 b7 lastStop hv7 hscan7
    let e7 : BlockEvidence decodeBlock blocks :=
      { index := 7#usize, bytes := b7, words := w7, stop := lastStop, selected := hblock7, decode_ok := hd7 }
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: [], s8, 7#usize, ?_, by simp, hv8, hfinish, hfacts.1, hfacts.2.symm, hadvance, by decide⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.cons hv6 hscan6 hq6 hv7 (Q22ScanChain.cons hv7 hscan7 hq7 hv8 (Q22ScanChain.nil s8 hv8))))))))


#print axioms driver_trace_q22_chain_with_finish
end Query31ConcreteDriverTraceFacts
end
