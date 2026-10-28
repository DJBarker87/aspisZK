import NDO_JFs_SerializerCanonical
import JFs_SerializerLengths
set_option autoImplicit false
namespace AspisR1.JFs_SerializerSize
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

theorem digest_length (a : Array U32 8#usize) : a.val.length=8 := a.property

theorem index_length (n : U64) : (core.num.U64.to_le_bytes n).val.length=8 := (core.num.U64.to_le_bytes n).property

theorem source : ((sourceSteps JFs_SerializerCanonical.value).flatMap stepBytes).length=1455 := by
  simp only [JFs_SerializerCanonical.value,AspisR1TerminalDecoder.PublicBinding.toSerializer,
    JFs_PublicValue.value,sourceSteps,tailSteps,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.length_append,stepBytes,JFs_SerializerLengths.words,
    JFs_SerializerLengths.frontier_words,index_length,
    AspisR1TerminalDecoder.PublicBinding.toTransfer,AspisR1TerminalDecoder.PublicBinding.toTransition,
    digest_length,single,Array.to_slice,Array.make,List.length_cons,List.length_nil]

#print axioms digest_length
#print axioms index_length
#print axioms source
end AspisR1.JFs_SerializerSize
