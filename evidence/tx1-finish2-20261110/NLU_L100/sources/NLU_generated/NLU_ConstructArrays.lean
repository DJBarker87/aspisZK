import NLU_ConstructCut
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (word cell)
theorem claims (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.claims=f.expected.claims := by
 apply NLU.cells_ext
 intro row hr
 apply NLU.cells_ext
 intro col hc
 exact NLU.word_ext _ _ ((cut f).1 ⟨row,hr⟩ ⟨col,hc⟩)
theorem alpha (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.alpha=f.expected.alpha := by
 apply NLU.cells_ext
 intro i hi
 exact NLU.word_ext _ _ ((cut f).2.1 ⟨i,hi⟩)
theorem roots (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.roots=f.expected.roots := by
 apply NLU.cells_ext
 intro row hr
 apply NLU.cells_ext
 intro byte hb
 exact (cut f).2.2.2.1 ⟨row,hr⟩ ⟨byte,hb⟩
#print axioms claims
#print axioms alpha
#print axioms roots
end AspisR1.NLU_Construct
