import NLU_ConstructCut
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (cell)
theorem transcript_ext (a b : r1_wire.SemanticTranscript Unit)
 (hs : a.state=b.state) (hn : a.next=b.next) : a=b := by
 cases a with
 | mk ah ast an=>
   cases b with
   | mk bh bst bn=>
     cases ah;cases bh;cases hs;cases hn;rfl
theorem transcript (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.transcript=f.expected.transcript := by
 apply transcript_ext
 · apply NLU.cells_ext;intro i hi
   exact (cut f).2.2.2.2.1 ⟨i,hi⟩
 · exact (cut f).2.2.2.2.2
#print axioms transcript_ext
#print axioms transcript
end AspisR1.NLU_Construct
