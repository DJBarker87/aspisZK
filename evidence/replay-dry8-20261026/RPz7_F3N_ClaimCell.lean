import RPz7_F3N_ClaimRowSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ClaimCell
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts

theorem successor (point i : Usize) (small : point.val<6)
    (increment : (point+1#usize : Result Usize)=ok i)
    (parts : Array E 7#usize) (hi : i.val<7) :
    cell parts i hi=parts.val[point.val+1]'(by have h : parts.val.length=7:=parts.property;omega) := by
  have bound : point.val+(1#usize).val≤UScalar.max .Usize := by scalar_tac
  have add := UScalar.add_spec (x:=point) (y:=1#usize) bound
  rw [increment] at add
  have index : i.val=point.val+1 := by simpa using add
  unfold cell
  simp only [index]

#print axioms successor
end AspisR1.F3N_ClaimCell
end
