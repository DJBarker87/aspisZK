import R1RecordFrameCodec
set_option autoImplicit false
namespace AspisR1.RecordFrameDropPayload
open FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
theorem drop_frame (tag : Byte) (payload : Bytes) :
    (RecordFrameCodec.frame tag payload).drop 5 = payload := by
  exact List.drop_left' (RecordFrameCodec.header_length tag payload.length)
#print axioms drop_frame
end AspisR1.RecordFrameDropPayload
