import Port5Q2_ReaderScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderFrame
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem raw (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (r out : verifier.Reader) (bytes : Array U8 N)
    (returned : verifier.Reader.rawWithUnwrap N unwrap r=ok (bytes,out)) : out.bytes=r.bytes := by
  unfold verifier.Reader.rawWithUnwrap at returned
  obtain ⟨end1,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ returned
  obtain ⟨slice,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨converted,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨array,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  have same := congrArg Prod.snd (Result.ok.inj h)
  exact (congrArg verifier.Reader.bytes same).symm

theorem readK (r out : verifier.Reader)
    (value : core.result.Result aspis_core.field.QM31 verifier.Error)
    (returned : CheckpointBytes3Reader.readK r=ok (value,out)) : out.bytes=r.bytes := by
  unfold CheckpointBytes3Reader.readK at returned
  obtain ⟨⟨bytes,rawOut⟩,called,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ returned
  obtain ⟨decoded,_,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  have same := congrArg Prod.snd (Result.ok.inj h)
  dsimp only at same
  have frame := raw 16#usize _ r rawOut bytes called
  exact (congrArg verifier.Reader.bytes same).symm.trans frame

#print axioms raw
#print axioms readK
end AspisR1.Port5Q2_ReaderFrame
end
