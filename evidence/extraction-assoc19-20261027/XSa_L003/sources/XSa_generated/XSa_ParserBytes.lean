import XSa_ParserWords
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_ParserBytes
open AspisR1.ExtractedRecordByteCanonicality

def toWide (x : AspisR1RecordParser.field.wide_exact.WideExact) : C.E :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem words (b : Array U8 32#usize) :
 (List.range 8).map (fun j => XRn_Join_word ((b.val.drop (4*j)).take 4)) =
 (wordArray8 b).val := by
 apply List.ext_getElem
 · simp only [List.length_map,List.length_range]
   exact (wordArray8 b).property.symm
 · intro i hi hj
   have hb : i<8 := by simpa only [List.length_map,List.length_range] using hi
   simp only [List.getElem_map,List.getElem_range]
   rw [XSa_ParserWords.word b ⟨i,hb⟩]
   interval_cases i <;> rfl

#print axioms words
end XSa_ParserBytes
