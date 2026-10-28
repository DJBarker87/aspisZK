import NDO_JFw_NativeRow00
import NDO_JFw_NativeRow01
import NDO_JFw_NativeRow02
import NDO_JFw_NativeRow03
import NDO_JFw_NativeRow04
import NDO_JFw_NativeRow05
import NDO_JFw_NativeRow06
import NDO_JFw_NativeRow07
import NDO_JFw_NativeRow08
import NDO_JFw_NativeRow09
import NDO_JFw_NativeRow10
import NDO_JFw_NativeRow11
import NDO_JFw_NativeRow12
import NDO_JFw_NativeRow13
import NDO_JFw_NativeRow14
import NDO_JFw_NativeRow15
import NDO_JFw_NativeRow16
import NDO_JFw_NativeRow17
import NDO_JFw_NativeRow18
import NDO_JFw_NativeRow19
import NDO_JFw_NativeRow20
import NDO_JFw_NativeRow21
import NDO_JFw_NativeRow22
import NDO_JFw_NativeRow23
import NDO_JFw_NativeRow24
import NDO_JFw_NativeRow25
import NDO_JFw_NativeRow26
import JFw_Chain
import NDO_JFw_FrameLength
import NDO_JFz_Parsed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_Records
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical
def frames : List (Slice U8) := [JFw_NativeRow00.record,JFw_NativeRow01.record,JFw_NativeRow02.record,JFw_NativeRow03.record,JFw_NativeRow04.record,JFw_NativeRow05.record,JFw_NativeRow06.record,JFw_NativeRow07.record,JFw_NativeRow08.record,JFw_NativeRow09.record,JFw_NativeRow10.record,JFw_NativeRow11.record,JFw_NativeRow12.record,JFw_NativeRow13.record,JFw_NativeRow14.record,JFw_NativeRow15.record,JFw_NativeRow16.record,JFw_NativeRow17.record,JFw_NativeRow18.record,JFw_NativeRow19.record,JFw_NativeRow20.record,JFw_NativeRow21.record,JFw_NativeRow22.record,JFw_NativeRow23.record,JFw_NativeRow24.record,JFw_NativeRow25.record,JFw_NativeRow26.record]
theorem bytes : frames.map (fun f => bytesOf f.val) = JFz_Parsed.rows00 := by
  simp only [frames,List.map_cons,List.map_nil]
  rw [JFw_NativeRow00.bytes,JFw_NativeRow01.bytes,JFw_NativeRow02.bytes,JFw_NativeRow03.bytes,JFw_NativeRow04.bytes,JFw_NativeRow05.bytes,JFw_NativeRow06.bytes,JFw_NativeRow07.bytes,JFw_NativeRow08.bytes,JFw_NativeRow09.bytes,JFw_NativeRow10.bytes,JFw_NativeRow11.bytes,JFw_NativeRow12.bytes,JFw_NativeRow13.bytes,JFw_NativeRow14.bytes,JFw_NativeRow15.bytes,JFw_NativeRow16.bytes,JFw_NativeRow17.bytes,JFw_NativeRow18.bytes,JFw_NativeRow19.bytes,JFw_NativeRow20.bytes,JFw_NativeRow21.bytes,JFw_NativeRow22.bytes,JFw_NativeRow23.bytes,JFw_NativeRow24.bytes,JFw_NativeRow25.bytes,JFw_NativeRow26.bytes]
  rfl
theorem checked : JFw_Chain.Checked ExtractedPrefixTrace.rowOrder frames := by
  unfold ExtractedPrefixTrace.rowOrder frames
  refine .cons JFw_NativeRow00.source_shape ?_ JFw_NativeRow00.accepted ?_
  · rw [JFw_NativeRow00.record,JFw_FrameLength.length,JFw_NativeRow00.payload_length];scalar_tac
  refine .cons JFw_NativeRow01.source_shape ?_ JFw_NativeRow01.accepted ?_
  · rw [JFw_NativeRow01.record,JFw_FrameLength.length,JFw_NativeRow01.payload_length];scalar_tac
  refine .cons JFw_NativeRow02.source_shape ?_ JFw_NativeRow02.accepted ?_
  · rw [JFw_NativeRow02.record,JFw_FrameLength.length,JFw_NativeRow02.payload_length];scalar_tac
  refine .cons JFw_NativeRow03.source_shape ?_ JFw_NativeRow03.accepted ?_
  · rw [JFw_NativeRow03.record,JFw_FrameLength.length,JFw_NativeRow03.payload_length];scalar_tac
  refine .cons JFw_NativeRow04.source_shape ?_ JFw_NativeRow04.accepted ?_
  · rw [JFw_NativeRow04.record,JFw_FrameLength.length,JFw_NativeRow04.payload_length];scalar_tac
  refine .cons JFw_NativeRow05.source_shape ?_ JFw_NativeRow05.accepted ?_
  · rw [JFw_NativeRow05.record,JFw_FrameLength.length,JFw_NativeRow05.payload_length];scalar_tac
  refine .cons JFw_NativeRow06.source_shape ?_ JFw_NativeRow06.accepted ?_
  · rw [JFw_NativeRow06.record,JFw_FrameLength.length,JFw_NativeRow06.payload_length];scalar_tac
  refine .cons JFw_NativeRow07.source_shape ?_ JFw_NativeRow07.accepted ?_
  · rw [JFw_NativeRow07.record,JFw_FrameLength.length,JFw_NativeRow07.payload_length];scalar_tac
  refine .cons JFw_NativeRow08.source_shape ?_ JFw_NativeRow08.accepted ?_
  · rw [JFw_NativeRow08.record,JFw_FrameLength.length,JFw_NativeRow08.payload_length];scalar_tac
  refine .cons JFw_NativeRow09.source_shape ?_ JFw_NativeRow09.accepted ?_
  · rw [JFw_NativeRow09.record,JFw_FrameLength.length,JFw_NativeRow09.payload_length];scalar_tac
  refine .cons JFw_NativeRow10.source_shape ?_ JFw_NativeRow10.accepted ?_
  · rw [JFw_NativeRow10.record,JFw_FrameLength.length,JFw_NativeRow10.payload_length];scalar_tac
  refine .cons JFw_NativeRow11.source_shape ?_ JFw_NativeRow11.accepted ?_
  · rw [JFw_NativeRow11.record,JFw_FrameLength.length,JFw_NativeRow11.payload_length];scalar_tac
  refine .cons JFw_NativeRow12.source_shape ?_ JFw_NativeRow12.accepted ?_
  · rw [JFw_NativeRow12.record,JFw_FrameLength.length,JFw_NativeRow12.payload_length];scalar_tac
  refine .cons JFw_NativeRow13.source_shape ?_ JFw_NativeRow13.accepted ?_
  · rw [JFw_NativeRow13.record,JFw_FrameLength.length,JFw_NativeRow13.payload_length];scalar_tac
  refine .cons JFw_NativeRow14.source_shape ?_ JFw_NativeRow14.accepted ?_
  · rw [JFw_NativeRow14.record,JFw_FrameLength.length,JFw_NativeRow14.payload_length];scalar_tac
  refine .cons JFw_NativeRow15.source_shape ?_ JFw_NativeRow15.accepted ?_
  · rw [JFw_NativeRow15.record,JFw_FrameLength.length,JFw_NativeRow15.payload_length];scalar_tac
  refine .cons JFw_NativeRow16.source_shape ?_ JFw_NativeRow16.accepted ?_
  · rw [JFw_NativeRow16.record,JFw_FrameLength.length,JFw_NativeRow16.payload_length];scalar_tac
  refine .cons JFw_NativeRow17.source_shape ?_ JFw_NativeRow17.accepted ?_
  · rw [JFw_NativeRow17.record,JFw_FrameLength.length,JFw_NativeRow17.payload_length];scalar_tac
  refine .cons JFw_NativeRow18.source_shape ?_ JFw_NativeRow18.accepted ?_
  · rw [JFw_NativeRow18.record,JFw_FrameLength.length,JFw_NativeRow18.payload_length];scalar_tac
  refine .cons JFw_NativeRow19.source_shape ?_ JFw_NativeRow19.accepted ?_
  · rw [JFw_NativeRow19.record,JFw_FrameLength.length,JFw_NativeRow19.payload_length];scalar_tac
  refine .cons JFw_NativeRow20.source_shape ?_ JFw_NativeRow20.accepted ?_
  · rw [JFw_NativeRow20.record,JFw_FrameLength.length,JFw_NativeRow20.payload_length];scalar_tac
  refine .cons JFw_NativeRow21.source_shape ?_ JFw_NativeRow21.accepted ?_
  · rw [JFw_NativeRow21.record,JFw_FrameLength.length,JFw_NativeRow21.payload_length];scalar_tac
  refine .cons JFw_NativeRow22.source_shape ?_ JFw_NativeRow22.accepted ?_
  · rw [JFw_NativeRow22.record,JFw_FrameLength.length,JFw_NativeRow22.payload_length];scalar_tac
  refine .cons JFw_NativeRow23.source_shape ?_ JFw_NativeRow23.accepted ?_
  · rw [JFw_NativeRow23.record,JFw_FrameLength.length,JFw_NativeRow23.payload_length];scalar_tac
  refine .cons JFw_NativeRow24.source_shape ?_ JFw_NativeRow24.accepted ?_
  · rw [JFw_NativeRow24.record,JFw_FrameLength.length,JFw_NativeRow24.payload_length];scalar_tac
  refine .cons JFw_NativeRow25.source_shape ?_ JFw_NativeRow25.accepted ?_
  · rw [JFw_NativeRow25.record,JFw_FrameLength.length,JFw_NativeRow25.payload_length];scalar_tac
  refine .cons JFw_NativeRow26.source_shape ?_ JFw_NativeRow26.accepted ?_
  · rw [JFw_NativeRow26.record,JFw_FrameLength.length,JFw_NativeRow26.payload_length];scalar_tac
  exact .nil
#print axioms bytes
#print axioms checked
end AspisR1.JFw_Records
end
