import JFs_SerializerProgram
import NDO_JFs_SerializerSize
set_option autoImplicit false
namespace AspisR1.JFs_SerializerSource
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Whole431

theorem source : ∃ encoded : ByteVec,
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      JFs_SerializerCanonical.value=ok (.Ok encoded) ∧
    encoded.val=(sourceSteps JFs_SerializerCanonical.value).flatMap stepBytes ∧
    encoded.val.length=1455 := by
  have cap : (alloc.vec.Vec.new U8).length+
      ((sourceSteps JFs_SerializerCanonical.value).flatMap stepBytes).length≤Usize.max := by
    rw [JFs_SerializerSize.source]
    change 0+1455≤Usize.max
    scalar_tac
  obtain ⟨encoded,call,bytes⟩:=JFs_SerializerProgram.source
    (sourceSteps JFs_SerializerCanonical.value) (alloc.vec.Vec.new U8)
    JFs_SerializerCanonical.source cap
  have contents : encoded.val=(sourceSteps JFs_SerializerCanonical.value).flatMap stepBytes := by
    simpa only [alloc.vec.Vec.new,List.nil_append] using bytes
  exact ⟨encoded,(source_eq_program _).trans call,contents,
    congrArg List.length contents |>.trans JFs_SerializerSize.source⟩

#print axioms source
end AspisR1.JFs_SerializerSource
