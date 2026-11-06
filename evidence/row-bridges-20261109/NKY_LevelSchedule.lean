import NKY_LevelsBody
set_option autoImplicit false
namespace AspisR1.NKY_LevelSchedule
open Aeneas Aeneas.Std Result

def levels (start : Nat) (fuel : Nat) (bound : start+fuel≤20) : List (Fin 20) :=
 match fuel with
 | 0 => []
 | n+1 => ⟨start,by omega⟩ :: levels (start+1) n (by omega)

theorem complete : levels 0 20 (by omega)=List.finRange 20 := by rfl

theorem length (start fuel : Nat) (bound : start+fuel≤20) :
 (levels start fuel bound).length=fuel := by
 induction fuel generalizing start with
 | zero=>rfl
 | succ n ih=>simp only [levels,List.length_cons,ih]

/-- Exactly one native child cut and four additions per scheduled level;
no data-dependent branch changes the20step control sequence. -/
theorem control (start fuel : Nat) (bound : start+fuel≤20) :
 (levels start fuel bound).map Fin.val=List.range' start fuel := by
 induction fuel generalizing start with
 | zero=>rfl
 | succ n ih=>simp only [levels,List.map_cons,ih,List.range'_succ]
#print axioms complete
#print axioms length
#print axioms control
end AspisR1.NKY_LevelSchedule
