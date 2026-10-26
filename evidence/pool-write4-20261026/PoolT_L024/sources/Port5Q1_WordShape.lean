import Port5Q1_Domain
set_option autoImplicit false
namespace AspisR1.Port5Q1_WordShape
open Aeneas Aeneas.Std
theorem length_words (x : U32) : (Port5Q1_Domain.words x.val).length=5 := by
  rfl
#print axioms length_words
end AspisR1.Port5Q1_WordShape
