import RPz7_F3P_CircleCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_GammaCell
open AspisV8R19.DuplexFrames

theorem decoded (bytes : Bytes) (values : OpeningRecordCodec.Payload .gamma)
    (h : OpeningRecordCodec.decode .gamma (LengthFrameCodec.frame bytes)=some values)
    (j : Fin 29) :
    SemanticCoefficientCodec.decodeLow ((bytes.drop (32*j.val)).take 32)=some (values j) := by
  obtain ⟨raw,framed,read⟩ := Option.bind_eq_some_iff.mp h
  have same := (LengthFrameCodec.parse_sound _ _ raw framed).2
  have actual : raw=bytes := by
    have full : LengthFrameCodec.frame bytes=LengthFrameCodec.frame raw := same
    have dropped := congrArg (List.drop 4) full
    simpa [LengthFrameCodec.frame,PublicInitFrame.lengthBytes] using dropped.symm
  subst raw
  exact (SelectedFieldSequenceCodec.decodeLow_eq_some_iff bytes values).mp read |>.2 j

#print axioms decoded
end AspisR1.F3P_GammaCell
end
