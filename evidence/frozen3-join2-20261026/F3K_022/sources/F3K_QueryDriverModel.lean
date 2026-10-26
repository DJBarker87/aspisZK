import F3K_QueryScanLast
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryDriverModel
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open Query31ExplicitListLoop Query31ExplicitScanBody
open R0C.V3

theorem driver (blocks advances : F3K_QueryScanStep.Blocks)
    (s0 : Query31ModelDriverChain.QueryScan) (accepted : Array U32 22#usize)
    (next : Array U8 32#usize) (initial : State)
    (valid0 : validState s0) (zero : (q22StateOf s0).draws=0)
    (trace : AspisR1Query31Transcript.DriverTrace
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      blocks advances s0 accepted next) :
    Q22.scanOut 8 (q22StateOf s0) (blocks.val.map decodeState) (advances.val.map decodeState) initial=
      (.ok (accepted.val.map (fun x=>x.val)),decodeState next) := by
  change Q22.scanOut 8 (q22StateOf s0) ((blocks.val.map decodeState).drop 0)
    ((advances.val.map decodeState).drop 0) initial=_
  have draw0 : (q22StateOf s0).draws<64 := by omega
  cases trace with
  | stop0 b0 s1 hblock0 hscan0 hfinish hadvance =>
    erw [F3K_QueryScanStep.stop blocks advances 0#usize 7 s0 s1 b0 next initial valid0 draw0 hblock0 hadvance hscan0,F3K_QueryScanCall.finish s1 accepted hfinish]
  | stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.stop blocks advances 1#usize 6 s1 s2 b1 next (decodeState x0) valid1 draw1 hblock1 hadvance hscan1,F3K_QueryScanCall.finish s2 accepted hfinish]
  | stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.stop blocks advances 2#usize 5 s2 s3 b2 next (decodeState x1) valid2 draw2 hblock2 hadvance hscan2,F3K_QueryScanCall.finish s3 accepted hfinish]
  | stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    have valid3 := (F3K_QueryScanCall.scan s2 s3 b2 false valid2 hscan2).2
    have progress2 := F3K_QueryScanStep.progress s2 s3 b2 valid2 hscan2
    have count3 : (q22StateOf s3).draws=24 := by omega
    have draw3 : (q22StateOf s3).draws<64 := by omega
    obtain ⟨x2,hx2⟩ := F3K_QueryScanStep.index_exists advances 2#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.more blocks advances 2#usize 5 s2 s3 b2 x2 (decodeState x1) valid2 draw2 hblock2 hx2 hscan2]
    erw [F3K_QueryScanStep.stop blocks advances 3#usize 4 s3 s4 b3 next (decodeState x2) valid3 draw3 hblock3 hadvance hscan3,F3K_QueryScanCall.finish s4 accepted hfinish]
  | stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    have valid3 := (F3K_QueryScanCall.scan s2 s3 b2 false valid2 hscan2).2
    have progress2 := F3K_QueryScanStep.progress s2 s3 b2 valid2 hscan2
    have count3 : (q22StateOf s3).draws=24 := by omega
    have draw3 : (q22StateOf s3).draws<64 := by omega
    obtain ⟨x2,hx2⟩ := F3K_QueryScanStep.index_exists advances 2#usize (by decide)
    have valid4 := (F3K_QueryScanCall.scan s3 s4 b3 false valid3 hscan3).2
    have progress3 := F3K_QueryScanStep.progress s3 s4 b3 valid3 hscan3
    have count4 : (q22StateOf s4).draws=32 := by omega
    have draw4 : (q22StateOf s4).draws<64 := by omega
    obtain ⟨x3,hx3⟩ := F3K_QueryScanStep.index_exists advances 3#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.more blocks advances 2#usize 5 s2 s3 b2 x2 (decodeState x1) valid2 draw2 hblock2 hx2 hscan2]
    erw [F3K_QueryScanStep.more blocks advances 3#usize 4 s3 s4 b3 x3 (decodeState x2) valid3 draw3 hblock3 hx3 hscan3]
    erw [F3K_QueryScanStep.stop blocks advances 4#usize 3 s4 s5 b4 next (decodeState x3) valid4 draw4 hblock4 hadvance hscan4,F3K_QueryScanCall.finish s5 accepted hfinish]
  | stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    have valid3 := (F3K_QueryScanCall.scan s2 s3 b2 false valid2 hscan2).2
    have progress2 := F3K_QueryScanStep.progress s2 s3 b2 valid2 hscan2
    have count3 : (q22StateOf s3).draws=24 := by omega
    have draw3 : (q22StateOf s3).draws<64 := by omega
    obtain ⟨x2,hx2⟩ := F3K_QueryScanStep.index_exists advances 2#usize (by decide)
    have valid4 := (F3K_QueryScanCall.scan s3 s4 b3 false valid3 hscan3).2
    have progress3 := F3K_QueryScanStep.progress s3 s4 b3 valid3 hscan3
    have count4 : (q22StateOf s4).draws=32 := by omega
    have draw4 : (q22StateOf s4).draws<64 := by omega
    obtain ⟨x3,hx3⟩ := F3K_QueryScanStep.index_exists advances 3#usize (by decide)
    have valid5 := (F3K_QueryScanCall.scan s4 s5 b4 false valid4 hscan4).2
    have progress4 := F3K_QueryScanStep.progress s4 s5 b4 valid4 hscan4
    have count5 : (q22StateOf s5).draws=40 := by omega
    have draw5 : (q22StateOf s5).draws<64 := by omega
    obtain ⟨x4,hx4⟩ := F3K_QueryScanStep.index_exists advances 4#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.more blocks advances 2#usize 5 s2 s3 b2 x2 (decodeState x1) valid2 draw2 hblock2 hx2 hscan2]
    erw [F3K_QueryScanStep.more blocks advances 3#usize 4 s3 s4 b3 x3 (decodeState x2) valid3 draw3 hblock3 hx3 hscan3]
    erw [F3K_QueryScanStep.more blocks advances 4#usize 3 s4 s5 b4 x4 (decodeState x3) valid4 draw4 hblock4 hx4 hscan4]
    erw [F3K_QueryScanStep.stop blocks advances 5#usize 2 s5 s6 b5 next (decodeState x4) valid5 draw5 hblock5 hadvance hscan5,F3K_QueryScanCall.finish s6 accepted hfinish]
  | stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    have valid3 := (F3K_QueryScanCall.scan s2 s3 b2 false valid2 hscan2).2
    have progress2 := F3K_QueryScanStep.progress s2 s3 b2 valid2 hscan2
    have count3 : (q22StateOf s3).draws=24 := by omega
    have draw3 : (q22StateOf s3).draws<64 := by omega
    obtain ⟨x2,hx2⟩ := F3K_QueryScanStep.index_exists advances 2#usize (by decide)
    have valid4 := (F3K_QueryScanCall.scan s3 s4 b3 false valid3 hscan3).2
    have progress3 := F3K_QueryScanStep.progress s3 s4 b3 valid3 hscan3
    have count4 : (q22StateOf s4).draws=32 := by omega
    have draw4 : (q22StateOf s4).draws<64 := by omega
    obtain ⟨x3,hx3⟩ := F3K_QueryScanStep.index_exists advances 3#usize (by decide)
    have valid5 := (F3K_QueryScanCall.scan s4 s5 b4 false valid4 hscan4).2
    have progress4 := F3K_QueryScanStep.progress s4 s5 b4 valid4 hscan4
    have count5 : (q22StateOf s5).draws=40 := by omega
    have draw5 : (q22StateOf s5).draws<64 := by omega
    obtain ⟨x4,hx4⟩ := F3K_QueryScanStep.index_exists advances 4#usize (by decide)
    have valid6 := (F3K_QueryScanCall.scan s5 s6 b5 false valid5 hscan5).2
    have progress5 := F3K_QueryScanStep.progress s5 s6 b5 valid5 hscan5
    have count6 : (q22StateOf s6).draws=48 := by omega
    have draw6 : (q22StateOf s6).draws<64 := by omega
    obtain ⟨x5,hx5⟩ := F3K_QueryScanStep.index_exists advances 5#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.more blocks advances 2#usize 5 s2 s3 b2 x2 (decodeState x1) valid2 draw2 hblock2 hx2 hscan2]
    erw [F3K_QueryScanStep.more blocks advances 3#usize 4 s3 s4 b3 x3 (decodeState x2) valid3 draw3 hblock3 hx3 hscan3]
    erw [F3K_QueryScanStep.more blocks advances 4#usize 3 s4 s5 b4 x4 (decodeState x3) valid4 draw4 hblock4 hx4 hscan4]
    erw [F3K_QueryScanStep.more blocks advances 5#usize 2 s5 s6 b5 x5 (decodeState x4) valid5 draw5 hblock5 hx5 hscan5]
    erw [F3K_QueryScanStep.stop blocks advances 6#usize 1 s6 s7 b6 next (decodeState x5) valid6 draw6 hblock6 hadvance hscan6,F3K_QueryScanCall.finish s7 accepted hfinish]
  | stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 lastStop hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hfinish hadvance =>
    have valid1 := (F3K_QueryScanCall.scan s0 s1 b0 false valid0 hscan0).2
    have progress0 := F3K_QueryScanStep.progress s0 s1 b0 valid0 hscan0
    have count1 : (q22StateOf s1).draws=8 := by omega
    have draw1 : (q22StateOf s1).draws<64 := by omega
    obtain ⟨x0,hx0⟩ := F3K_QueryScanStep.index_exists advances 0#usize (by decide)
    have valid2 := (F3K_QueryScanCall.scan s1 s2 b1 false valid1 hscan1).2
    have progress1 := F3K_QueryScanStep.progress s1 s2 b1 valid1 hscan1
    have count2 : (q22StateOf s2).draws=16 := by omega
    have draw2 : (q22StateOf s2).draws<64 := by omega
    obtain ⟨x1,hx1⟩ := F3K_QueryScanStep.index_exists advances 1#usize (by decide)
    have valid3 := (F3K_QueryScanCall.scan s2 s3 b2 false valid2 hscan2).2
    have progress2 := F3K_QueryScanStep.progress s2 s3 b2 valid2 hscan2
    have count3 : (q22StateOf s3).draws=24 := by omega
    have draw3 : (q22StateOf s3).draws<64 := by omega
    obtain ⟨x2,hx2⟩ := F3K_QueryScanStep.index_exists advances 2#usize (by decide)
    have valid4 := (F3K_QueryScanCall.scan s3 s4 b3 false valid3 hscan3).2
    have progress3 := F3K_QueryScanStep.progress s3 s4 b3 valid3 hscan3
    have count4 : (q22StateOf s4).draws=32 := by omega
    have draw4 : (q22StateOf s4).draws<64 := by omega
    obtain ⟨x3,hx3⟩ := F3K_QueryScanStep.index_exists advances 3#usize (by decide)
    have valid5 := (F3K_QueryScanCall.scan s4 s5 b4 false valid4 hscan4).2
    have progress4 := F3K_QueryScanStep.progress s4 s5 b4 valid4 hscan4
    have count5 : (q22StateOf s5).draws=40 := by omega
    have draw5 : (q22StateOf s5).draws<64 := by omega
    obtain ⟨x4,hx4⟩ := F3K_QueryScanStep.index_exists advances 4#usize (by decide)
    have valid6 := (F3K_QueryScanCall.scan s5 s6 b5 false valid5 hscan5).2
    have progress5 := F3K_QueryScanStep.progress s5 s6 b5 valid5 hscan5
    have count6 : (q22StateOf s6).draws=48 := by omega
    have draw6 : (q22StateOf s6).draws<64 := by omega
    obtain ⟨x5,hx5⟩ := F3K_QueryScanStep.index_exists advances 5#usize (by decide)
    have valid7 := (F3K_QueryScanCall.scan s6 s7 b6 false valid6 hscan6).2
    have progress6 := F3K_QueryScanStep.progress s6 s7 b6 valid6 hscan6
    have count7 : (q22StateOf s7).draws=56 := by omega
    have draw7 : (q22StateOf s7).draws<64 := by omega
    obtain ⟨x6,hx6⟩ := F3K_QueryScanStep.index_exists advances 6#usize (by decide)
    erw [F3K_QueryScanStep.more blocks advances 0#usize 7 s0 s1 b0 x0 initial valid0 draw0 hblock0 hx0 hscan0]
    erw [F3K_QueryScanStep.more blocks advances 1#usize 6 s1 s2 b1 x1 (decodeState x0) valid1 draw1 hblock1 hx1 hscan1]
    erw [F3K_QueryScanStep.more blocks advances 2#usize 5 s2 s3 b2 x2 (decodeState x1) valid2 draw2 hblock2 hx2 hscan2]
    erw [F3K_QueryScanStep.more blocks advances 3#usize 4 s3 s4 b3 x3 (decodeState x2) valid3 draw3 hblock3 hx3 hscan3]
    erw [F3K_QueryScanStep.more blocks advances 4#usize 3 s4 s5 b4 x4 (decodeState x3) valid4 draw4 hblock4 hx4 hscan4]
    erw [F3K_QueryScanStep.more blocks advances 5#usize 2 s5 s6 b5 x5 (decodeState x4) valid5 draw5 hblock5 hx5 hscan5]
    erw [F3K_QueryScanStep.more blocks advances 6#usize 1 s6 s7 b6 x6 (decodeState x5) valid6 draw6 hblock6 hx6 hscan6]
    erw [F3K_QueryScanLast.last blocks advances 7#usize s7 s8 b7 next (decodeState x6) valid7 draw7 hblock7 hadvance lastStop hscan7,F3K_QueryScanCall.finish s8 accepted hfinish]

#print axioms driver
end AspisR1.F3K_QueryDriverModel
end
