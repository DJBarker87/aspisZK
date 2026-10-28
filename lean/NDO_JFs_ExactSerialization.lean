import NDO_JFs_SerializedBytes
set_option autoImplicit false
namespace AspisR1.JFs_ExactSerialization
open Aeneas Aeneas.Std Result

theorem length : JFs_SerializedBytes.bytes.length=1455 := by
  rw [←JFs_SerializedBytes.source]
  exact JFs_SerializerSize.source

def encoded : alloc.vec.Vec U8 := ⟨JFs_SerializedBytes.bytes,by rw [length];scalar_tac⟩

theorem source : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
    JFs_PublicSerialization.value=ok (.Ok encoded) := by
  obtain ⟨actual,call,contents,size⟩:=JFs_PublicSerialization.source
  have same : actual=encoded := Subtype.ext (contents.trans JFs_SerializedBytes.source)
  exact same ▸ call

#print axioms length
#print axioms source
end AspisR1.JFs_ExactSerialization
