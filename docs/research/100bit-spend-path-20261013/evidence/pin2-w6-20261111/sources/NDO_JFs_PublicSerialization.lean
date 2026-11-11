import NDO_JFs_SerializerSource
import JFs_SerializerReflect
import ExtractedPublicPreparationBinding
set_option autoImplicit false
namespace AspisR1.JFs_PublicSerialization
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def value := PreparationBinding.preparationPublic JFs_PublicValue.value

/- PIN2 W6: `value` (the frozen preparation carrier of the decoded statement) is
   unchanged; the serializer is now the PIN2 `public_bytes` applied to W3c's field-for-field
   `PreparationBinding.toPIN2 value`, which `projection_eq` identifies with
   `JFs_SerializerCanonical.value`.  Length 1520 (was 1455).  The release step through
   `JFs_SerializerReflect` (frozen 4.31 serializer = frozen preparation serializer) is no
   longer needed. -/
theorem source : ∃ encoded : alloc.vec.Vec U8,
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (PreparationBinding.toPIN2 value)=ok (.Ok encoded) ∧
    encoded.val=(AspisR1.PIN2_PublicBytesRefinement.steps JFs_SerializerCanonical.value).flatMap
      AspisR1.PIN2_PublicBytesRefinement.stepBytes ∧ encoded.val.length=1520 := by
  obtain ⟨encoded,call,bytes,length⟩:=JFs_SerializerSource.source
  have same : PreparationBinding.toPIN2 value=JFs_SerializerCanonical.value :=
    PreparationBinding.projection_eq JFs_PublicValue.value
  rw [same]
  exact ⟨encoded,call,bytes,length⟩

#print axioms source
end AspisR1.JFs_PublicSerialization
