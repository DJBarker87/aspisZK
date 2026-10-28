import NDI_TranscriptLaw
set_option autoImplicit false
namespace NDI_TranscriptInit
open Aeneas Aeneas.Std Result

theorem length_conversion (publicBytes : Slice U8) (cap : publicBytes.val.length≤1880) :
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len publicBytes) =
      ok (.Ok (UScalar.cast .U32 (Slice.len publicBytes))) := by
  have bound : (Slice.len publicBytes).val ≤ UScalar.max .U32 := by scalar_tac
  simp only [core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
    core.num.tryFromUScalar,if_pos bound]

theorem reference {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root reply : NDI_TranscriptLaw.Bytes32)
    (cap : publicBytes.val.length≤1880)
    (digest : D.digest hash (NDI_TranscriptLaw.newParts publicBytes root
      (UScalar.cast .U32 (Slice.len publicBytes)))=ok reply) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D hash publicBytes root =
      ok (.Ok {state:=reply,hash:=hash,next_row:=0#u8}) := by
  unfold NDI_TranscriptLaw.newParts at digest
  simp only [AspisR1PublicPreparation.r1_wire.SemanticTranscript.new,
    length_conversion publicBytes cap,AspisR1PublicPreparation.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,lift,bind_tc_ok,digest]

#print axioms length_conversion
#print axioms reference
end NDI_TranscriptInit
