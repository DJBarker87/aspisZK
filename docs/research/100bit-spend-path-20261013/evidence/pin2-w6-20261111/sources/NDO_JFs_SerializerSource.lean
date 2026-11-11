import JFs_SerializerProgram
import NDO_JFs_SerializerSize
import PIN2W6_SerializerProgram
set_option autoImplicit false
namespace AspisR1.JFs_SerializerSource
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Whole431

/- PIN2 W6: the generated entry point is the PIN2 `public_bytes` (Stream C emission,
   `PIN2_NEWGATE_r0`); length 1520 (was 1455).  Success comes from
   `PIN2W6_SerializerProgram.public_bytes` (canonical words + capacity, the release premises). -/
theorem source : ∃ encoded : ByteVec,
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      JFs_SerializerCanonical.value=ok (.Ok encoded) ∧
    encoded.val=(AspisR1.PIN2_PublicBytesRefinement.steps JFs_SerializerCanonical.value).flatMap
      AspisR1.PIN2_PublicBytesRefinement.stepBytes ∧
    encoded.val.length=1520 := by
  have cap : ((AspisR1.PIN2_PublicBytesRefinement.steps JFs_SerializerCanonical.value).flatMap
      AspisR1.PIN2_PublicBytesRefinement.stepBytes).length≤Usize.max := by
    rw [JFs_SerializerSize.source]
    scalar_tac
  obtain ⟨encoded,call,contents⟩:=PIN2W6_SerializerProgram.public_bytes _ JFs_SerializerCanonical.source cap
  exact ⟨encoded,call,contents,congrArg List.length contents |>.trans JFs_SerializerSize.source⟩

#print axioms source
end AspisR1.JFs_SerializerSource
