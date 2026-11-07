import NNH_ValueOk
set_option autoImplicit false
namespace NNH_OptionOk
open RSL NND_Returned

theorem value {A : Type} (x : Option A) (e : ProgramError) (a : A)
 (success : option x e=.ok a) : x=some a := by
 cases x with
 | none => cases success
 | some b => exact congrArg some (Except.ok.inj success)

#print axioms value
end NNH_OptionOk
