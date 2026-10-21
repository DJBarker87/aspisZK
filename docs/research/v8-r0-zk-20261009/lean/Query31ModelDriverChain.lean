import Query31ModelScanCall
import Query31UnrolledDriverFirstStop
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ModelDriverChain
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ExplicitListLoop Query31ExplicitScanBody Query31ModelScanCall

abbrev QueryScan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan

structure BlockEvidence
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (blocks : Array (Array Std.U8 32#usize) 8#usize) where
  index : Std.Usize
  bytes : Array Std.U8 32#usize
  words : Array Std.U32 8#usize
  stop : Bool
  selected : Array.index_usize blocks index = .ok bytes
  decode_ok : decodeBlock bytes = .ok words

inductive Q22ScanChain
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (blocks : Array (Array Std.U8 32#usize) 8#usize) :
    QueryScan → List (BlockEvidence decodeBlock blocks) → QueryScan → Prop where
  | nil (s : QueryScan) (hs : validState s) : Q22ScanChain decodeBlock blocks s [] s
  | cons {s s' sf : QueryScan} {e : BlockEvidence decodeBlock blocks}
      {rest : List (BlockEvidence decodeBlock blocks)}
      (hs : validState s)
      (hcall : modelScanFn decodeBlock s e.bytes = .ok (e.stop, s'))
      (hsemantic : scan (q22StateOf s) (e.words.val.map (fun x => x.val)) =
        (q22StateOf s', e.stop))
      (hvalid : validState s')
      (htail : Q22ScanChain decodeBlock blocks s' rest sf) :
      Q22ScanChain decodeBlock blocks s (e :: rest) sf

/-- A successful first-stop driver call sequence can be replayed as one
    state-valid Q22 chain. Each block/decode/output triple is tied to the same
    scan call in the supplied DriverTrace; byte-to-word decoding is explicit. -/
theorem driver_trace_q22_chain
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : QueryScan) (accepted : Array Std.U32 22#usize)
    (next : Array Std.U8 32#usize)
    (hstart : validState s0)
    (htrace : AspisR1Query31Transcript.DriverTrace
      (modelScanFn decodeBlock) blocks advances s0 accepted next) :
    ∃ evidence sf,
      Q22ScanChain decodeBlock blocks s0 evidence sf ∧
      evidence.length ≤ 8 ∧ validState sf := by
  cases htrace with
  | stop0 b0 s1 hblock0 hscan0 hfinish hadvance =>
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 true hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := true, selected := hblock0, decode_ok := hd0 }
    refine ⟨e0 :: [], s1, ?_, by simp, hv1⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.nil s1 hv1)
  | stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hfinish hadvance =>
    obtain ⟨w0, hd0, hq0, hv1⟩ :=
      modelScanFn_success decodeBlock s0 s1 b0 false hstart hscan0
    let e0 : BlockEvidence decodeBlock blocks :=
      { index := 0#usize, bytes := b0, words := w0, stop := false, selected := hblock0, decode_ok := hd0 }
    obtain ⟨w1, hd1, hq1, hv2⟩ :=
      modelScanFn_success decodeBlock s1 s2 b1 true hv1 hscan1
    let e1 : BlockEvidence decodeBlock blocks :=
      { index := 1#usize, bytes := b1, words := w1, stop := true, selected := hblock1, decode_ok := hd1 }
    refine ⟨e0 :: e1 :: [], s2, ?_, by simp, hv2⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.nil s2 hv2))
  | stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: [], s3, ?_, by simp, hv3⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.nil s3 hv3)))
  | stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: e3 :: [], s4, ?_, by simp, hv4⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.nil s4 hv4))))
  | stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: [], s5, ?_, by simp, hv5⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.nil s5 hv5)))))
  | stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: [], s6, ?_, by simp, hv6⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.nil s6 hv6))))))
  | stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: [], s7, ?_, by simp, hv7⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.cons hv6 hscan6 hq6 hv7 (Q22ScanChain.nil s7 hv7)))))))
  | stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 lastStop hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hfinish hadvance =>
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
    refine ⟨e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: [], s8, ?_, by simp, hv8⟩
    exact Q22ScanChain.cons hstart hscan0 hq0 hv1 (Q22ScanChain.cons hv1 hscan1 hq1 hv2 (Q22ScanChain.cons hv2 hscan2 hq2 hv3 (Q22ScanChain.cons hv3 hscan3 hq3 hv4 (Q22ScanChain.cons hv4 hscan4 hq4 hv5 (Q22ScanChain.cons hv5 hscan5 hq5 hv6 (Q22ScanChain.cons hv6 hscan6 hq6 hv7 (Q22ScanChain.cons hv7 hscan7 hq7 hv8 (Q22ScanChain.nil s8 hv8))))))))

/-- Full modeled driver success inherits the Q22 chain from the exact
    first-stop decomposition. The selected advance/finish facts remain in the
    DriverTrace supplied to the theorem; only the decoder operation remains explicit. -/
theorem successful_driver_q22_chain
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : QueryScan) (accepted : Array Std.U32 22#usize)
    (next : Array Std.U8 32#usize)
    (hstart : validState s0)
    (hsuccess : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (modelScanFn decodeBlock) s0 blocks advances =
        .ok (core.result.Result.Ok (accepted, next))) :
    ∃ evidence sf,
      Q22ScanChain decodeBlock blocks s0 evidence sf ∧
      evidence.length ≤ 8 ∧ validState sf := by
  let trace := AspisR1Query31Transcript.successful_driver_has_trace
    (modelScanFn decodeBlock) s0 blocks advances accepted next hsuccess
  obtain ⟨evidence, sf, hchain, hlen, hvalid⟩ :=
    driver_trace_q22_chain decodeBlock blocks advances s0 accepted next hstart trace
  exact ⟨evidence, sf, hchain, hlen, hvalid⟩

#print axioms driver_trace_q22_chain
#print axioms successful_driver_q22_chain
end Query31ModelDriverChain
