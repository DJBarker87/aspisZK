import NLU_ConstructCut
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (word cell)
theorem point_ext (a b : aspis_core.circle.SecureCirclePoint) (hx : a.x=b.x) (hy : a.y=b.y) : a=b := by
 cases a;cases b;cases hx;cases hy;rfl
theorem points (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.z=f.expected.z := by
 apply NLU.cells_ext
 intro i hi
 have options : i=0 ∨ i=1 := by omega
 rcases options with rfl|rfl
 · apply point_ext
   · apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
     exact (cut f).2.2.1 ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
   · apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
     exact (cut f).2.2.1 ⟨9,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
 · apply point_ext
   · apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
     exact (cut f).2.2.1 ⟨10,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
   · apply NLU.word_ext;intro j;apply UScalar.eq_of_val_eq
     exact (cut f).2.2.1 ⟨11,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
#print axioms point_ext
#print axioms points
end AspisR1.NLU_Construct
