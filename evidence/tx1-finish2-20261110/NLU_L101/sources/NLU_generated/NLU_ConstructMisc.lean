import NLU_ConstructCut
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (word cell)
theorem extra (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.extra=f.expected.extra := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 exact (cut f).2.2.1 ⟨0,by decide⟩ ⟨i,hi⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
theorem before (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.before_z1=f.expected.before_z1 := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 exact (cut f).2.2.1 ⟨1,by decide⟩ ⟨i,hi⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ j
theorem state (native : Native) (cut : Cut native) (f : Frame) :
 (native f).value.state_before_z0=f.expected.state_before_z0 := by
 apply NLU.cells_ext
 intro i hi
 apply UScalar.eq_of_val_eq
 exact (cut f).2.2.1 ⟨12,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨i,hi⟩ ⟨0,by decide⟩
#print axioms extra
#print axioms before
#print axioms state
end AspisR1.NLU_Construct
