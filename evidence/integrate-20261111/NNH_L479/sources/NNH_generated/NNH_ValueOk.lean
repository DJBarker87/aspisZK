import NNH_ReturnsBundle
set_option autoImplicit false
namespace NNH_ValueOk
open RSL NND_Returned

theorem bind {A B : Type} (x : Except ProgramError A) (k : A → Except ProgramError B) (out : B)
 (ok : ebind x k=.ok out) : ∃ a,x=.ok a ∧ k a=.ok out := by
 cases x with
 | error e => cases ok
 | ok a => exact ⟨a,rfl,ok⟩

theorem seq {A : Type} (x : Except ProgramError Unit) (y : Except ProgramError A) (out : A)
 (ok : eseq x y=.ok out) : x=.ok () ∧ y=.ok out := by
 cases x with
 | error e => cases ok
 | ok unit => cases unit; exact ⟨rfl,ok⟩
#print axioms bind
#print axioms seq
end NNH_ValueOk
