import S1QueryScanModelStepV1
import Query31ConcreteDriverTraceFacts
set_option autoImplicit false
noncomputable section
namespace AspisS1QueryScanModel
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open AspisV8R19.Q22WordScan
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ModelScanCall
open Query31ConcreteWordsDriverChain

/-- ACCEPTED-ONLY: the existing source driver's SAME successful result
identifies both the ordered queries and the selected mathematical state.
The zero-draw premise is discharged by the concrete default wrapper below. -/
theorem driver_trace_scanOut (blocks advances : Blocks8) (s0 : QueryScan)
    (accepted : Array U32 22#usize) (next : Bytes32) (start : State)
    (valid : validState s0) (zeroDraws : s0.draws.val=0)
    (trace : AspisR1Query31Transcript.DriverTrace (modelScanFn actualQueryWords)
      blocks advances s0 accepted next) :
    R0C.V3.Q22.scanOut 8 (q22StateOf s0)
      (statesFrom blocks 0) (statesFrom advances 0) start=
        (.ok (accepted.val.map (fun w => w.val)),decodeState next) := by
  cases trace with
  | stop0 b0 s1 hblock0 hscan0 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 true valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 true valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 true start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 0#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 0#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 true valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 true valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 true (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 1#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 1#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 true valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 true valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 true (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 2#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 2#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 false valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 false valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 false (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid4 := (source_scan_math s3 s4 b3 true valid3 hscan3).2
    have bound4 := source_scan_draw_le s3 s4 b3 true valid3 hscan3
    have draw3 : s3.draws.val<64 := by omega
    have step3 := scanOut_source_step 4 s3 s4 blocks advances 3#usize (by decide) b3 true (decodeState (blockAt advances 2#usize (by decide))) valid3 draw3 hblock3 hscan3
    simp only [show (3#usize : Usize).val=3 from by scalar_tac] at step3
    rw [step3]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 3#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 3#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 false valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 false valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 false (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid4 := (source_scan_math s3 s4 b3 false valid3 hscan3).2
    have bound4 := source_scan_draw_le s3 s4 b3 false valid3 hscan3
    have draw3 : s3.draws.val<64 := by omega
    have step3 := scanOut_source_step 4 s3 s4 blocks advances 3#usize (by decide) b3 false (decodeState (blockAt advances 2#usize (by decide))) valid3 draw3 hblock3 hscan3
    simp only [show (3#usize : Usize).val=3 from by scalar_tac] at step3
    rw [step3]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid5 := (source_scan_math s4 s5 b4 true valid4 hscan4).2
    have bound5 := source_scan_draw_le s4 s5 b4 true valid4 hscan4
    have draw4 : s4.draws.val<64 := by omega
    have step4 := scanOut_source_step 3 s4 s5 blocks advances 4#usize (by decide) b4 true (decodeState (blockAt advances 3#usize (by decide))) valid4 draw4 hblock4 hscan4
    simp only [show (4#usize : Usize).val=4 from by scalar_tac] at step4
    rw [step4]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 4#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 4#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 false valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 false valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 false (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid4 := (source_scan_math s3 s4 b3 false valid3 hscan3).2
    have bound4 := source_scan_draw_le s3 s4 b3 false valid3 hscan3
    have draw3 : s3.draws.val<64 := by omega
    have step3 := scanOut_source_step 4 s3 s4 blocks advances 3#usize (by decide) b3 false (decodeState (blockAt advances 2#usize (by decide))) valid3 draw3 hblock3 hscan3
    simp only [show (3#usize : Usize).val=3 from by scalar_tac] at step3
    rw [step3]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid5 := (source_scan_math s4 s5 b4 false valid4 hscan4).2
    have bound5 := source_scan_draw_le s4 s5 b4 false valid4 hscan4
    have draw4 : s4.draws.val<64 := by omega
    have step4 := scanOut_source_step 3 s4 s5 blocks advances 4#usize (by decide) b4 false (decodeState (blockAt advances 3#usize (by decide))) valid4 draw4 hblock4 hscan4
    simp only [show (4#usize : Usize).val=4 from by scalar_tac] at step4
    rw [step4]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid6 := (source_scan_math s5 s6 b5 true valid5 hscan5).2
    have bound6 := source_scan_draw_le s5 s6 b5 true valid5 hscan5
    have draw5 : s5.draws.val<64 := by omega
    have step5 := scanOut_source_step 2 s5 s6 blocks advances 5#usize (by decide) b5 true (decodeState (blockAt advances 4#usize (by decide))) valid5 draw5 hblock5 hscan5
    simp only [show (5#usize : Usize).val=5 from by scalar_tac] at step5
    rw [step5]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 5#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 5#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 false valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 false valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 false (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid4 := (source_scan_math s3 s4 b3 false valid3 hscan3).2
    have bound4 := source_scan_draw_le s3 s4 b3 false valid3 hscan3
    have draw3 : s3.draws.val<64 := by omega
    have step3 := scanOut_source_step 4 s3 s4 blocks advances 3#usize (by decide) b3 false (decodeState (blockAt advances 2#usize (by decide))) valid3 draw3 hblock3 hscan3
    simp only [show (3#usize : Usize).val=3 from by scalar_tac] at step3
    rw [step3]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid5 := (source_scan_math s4 s5 b4 false valid4 hscan4).2
    have bound5 := source_scan_draw_le s4 s5 b4 false valid4 hscan4
    have draw4 : s4.draws.val<64 := by omega
    have step4 := scanOut_source_step 3 s4 s5 blocks advances 4#usize (by decide) b4 false (decodeState (blockAt advances 3#usize (by decide))) valid4 draw4 hblock4 hscan4
    simp only [show (4#usize : Usize).val=4 from by scalar_tac] at step4
    rw [step4]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid6 := (source_scan_math s5 s6 b5 false valid5 hscan5).2
    have bound6 := source_scan_draw_le s5 s6 b5 false valid5 hscan5
    have draw5 : s5.draws.val<64 := by omega
    have step5 := scanOut_source_step 2 s5 s6 blocks advances 5#usize (by decide) b5 false (decodeState (blockAt advances 4#usize (by decide))) valid5 draw5 hblock5 hscan5
    simp only [show (5#usize : Usize).val=5 from by scalar_tac] at step5
    rw [step5]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid7 := (source_scan_math s6 s7 b6 true valid6 hscan6).2
    have bound7 := source_scan_draw_le s6 s7 b6 true valid6 hscan6
    have draw6 : s6.draws.val<64 := by omega
    have step6 := scanOut_source_step 1 s6 s7 blocks advances 6#usize (by decide) b6 true (decodeState (blockAt advances 5#usize (by decide))) valid6 draw6 hblock6 hscan6
    simp only [show (6#usize : Usize).val=6 from by scalar_tac] at step6
    rw [step6]
    simp only [Bool.false_eq_true,if_false,if_true]
    have nextEq : blockAt advances 6#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 6#usize (by decide)).symm.trans hadvance)
    rw [source_finish_math _ _ hfinish,nextEq]
  | stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 lastStop hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hfinish hadvance =>
    have valid0 := valid
    have valid1 := (source_scan_math s0 s1 b0 false valid0 hscan0).2
    have bound1 := source_scan_draw_le s0 s1 b0 false valid0 hscan0
    have draw0 : s0.draws.val<64 := by omega
    have step0 := scanOut_source_step 7 s0 s1 blocks advances 0#usize (by decide) b0 false start valid0 draw0 hblock0 hscan0
    simp only [show (0#usize : Usize).val=0 from by scalar_tac] at step0
    rw [step0]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid2 := (source_scan_math s1 s2 b1 false valid1 hscan1).2
    have bound2 := source_scan_draw_le s1 s2 b1 false valid1 hscan1
    have draw1 : s1.draws.val<64 := by omega
    have step1 := scanOut_source_step 6 s1 s2 blocks advances 1#usize (by decide) b1 false (decodeState (blockAt advances 0#usize (by decide))) valid1 draw1 hblock1 hscan1
    simp only [show (1#usize : Usize).val=1 from by scalar_tac] at step1
    rw [step1]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid3 := (source_scan_math s2 s3 b2 false valid2 hscan2).2
    have bound3 := source_scan_draw_le s2 s3 b2 false valid2 hscan2
    have draw2 : s2.draws.val<64 := by omega
    have step2 := scanOut_source_step 5 s2 s3 blocks advances 2#usize (by decide) b2 false (decodeState (blockAt advances 1#usize (by decide))) valid2 draw2 hblock2 hscan2
    simp only [show (2#usize : Usize).val=2 from by scalar_tac] at step2
    rw [step2]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid4 := (source_scan_math s3 s4 b3 false valid3 hscan3).2
    have bound4 := source_scan_draw_le s3 s4 b3 false valid3 hscan3
    have draw3 : s3.draws.val<64 := by omega
    have step3 := scanOut_source_step 4 s3 s4 blocks advances 3#usize (by decide) b3 false (decodeState (blockAt advances 2#usize (by decide))) valid3 draw3 hblock3 hscan3
    simp only [show (3#usize : Usize).val=3 from by scalar_tac] at step3
    rw [step3]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid5 := (source_scan_math s4 s5 b4 false valid4 hscan4).2
    have bound5 := source_scan_draw_le s4 s5 b4 false valid4 hscan4
    have draw4 : s4.draws.val<64 := by omega
    have step4 := scanOut_source_step 3 s4 s5 blocks advances 4#usize (by decide) b4 false (decodeState (blockAt advances 3#usize (by decide))) valid4 draw4 hblock4 hscan4
    simp only [show (4#usize : Usize).val=4 from by scalar_tac] at step4
    rw [step4]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid6 := (source_scan_math s5 s6 b5 false valid5 hscan5).2
    have bound6 := source_scan_draw_le s5 s6 b5 false valid5 hscan5
    have draw5 : s5.draws.val<64 := by omega
    have step5 := scanOut_source_step 2 s5 s6 blocks advances 5#usize (by decide) b5 false (decodeState (blockAt advances 4#usize (by decide))) valid5 draw5 hblock5 hscan5
    simp only [show (5#usize : Usize).val=5 from by scalar_tac] at step5
    rw [step5]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid7 := (source_scan_math s6 s7 b6 false valid6 hscan6).2
    have bound7 := source_scan_draw_le s6 s7 b6 false valid6 hscan6
    have draw6 : s6.draws.val<64 := by omega
    have step6 := scanOut_source_step 1 s6 s7 blocks advances 6#usize (by decide) b6 false (decodeState (blockAt advances 5#usize (by decide))) valid6 draw6 hblock6 hscan6
    simp only [show (6#usize : Usize).val=6 from by scalar_tac] at step6
    rw [step6]
    simp only [Bool.false_eq_true,if_false,if_true]
    have valid8 := (source_scan_math s7 s8 b7 lastStop valid7 hscan7).2
    have bound8 := source_scan_draw_le s7 s8 b7 lastStop valid7 hscan7
    have draw7 : s7.draws.val<64 := by omega
    have step7 := scanOut_source_step 0 s7 s8 blocks advances 7#usize (by decide) b7 lastStop (decodeState (blockAt advances 6#usize (by decide))) valid7 draw7 hblock7 hscan7
    simp only [show (7#usize : Usize).val=7 from by scalar_tac] at step7
    rw [step7]
    have nextEq : blockAt advances 7#usize (by decide)=next :=
      Result.ok.inj ((blockAt_selected advances 7#usize (by decide)).symm.trans hadvance)
    cases lastStop <;> simp only [Bool.false_eq_true,if_false,if_true,R0C.V3.Q22.scanOut]
    all_goals
      rw [source_finish_math _ _ hfinish,nextEq]

/-- Concrete default state: no separate valid-state or counter premise. -/
theorem default_driver_scanOut (blocks advances : Blocks8)
    (accepted : Array U32 22#usize) (next : Bytes32) (start : State)
    (success : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (modelScanFn actualQueryWords) Query31ConcreteDriverTraceFacts.sourceDefaultState
      blocks advances=ok (.Ok (accepted,next))) :
    R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (blocks.val.map decodeState) (advances.val.map decodeState) start=
        (.ok (accepted.val.map (fun w => w.val)),decodeState next) := by
  have trace := AspisR1Query31Transcript.successful_driver_has_trace _ _ _ _ _ _ success
  have result := driver_trace_scanOut blocks advances _ accepted next start
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid rfl trace
  simpa only [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22,
    R0C.V3.Q22.q0,statesFrom,List.drop_zero] using result

#print axioms driver_trace_scanOut
#print axioms default_driver_scanOut
end AspisS1QueryScanModel
