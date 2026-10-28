import NDO_JFs_SerializerSource
import JFs_SerializerReflect
import ExtractedPublicPreparationBinding
set_option autoImplicit false
namespace AspisR1.JFs_PublicSerialization
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def value := PreparationBinding.preparationPublic JFs_PublicValue.value

theorem source : ∃ encoded : alloc.vec.Vec U8,
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes value=ok (.Ok encoded) ∧
    encoded.val=(AspisR1PublicSerializer.Whole431.sourceSteps JFs_SerializerCanonical.value).flatMap
      AspisR1PublicSerializer.Whole431.stepBytes ∧ encoded.val.length=1455 := by
  obtain ⟨encoded,old,bytes,length⟩:=JFs_SerializerSource.source
  have oldCall : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (SerializerWhole.toOld value)=ok (.Ok encoded) := by
    simpa only [value,PreparationBinding.projection_eq,JFs_SerializerCanonical.value] using old
  exact ⟨encoded,JFs_SerializerReflect.source value encoded oldCall,bytes,length⟩

#print axioms source
end AspisR1.JFs_PublicSerialization
