import NNH_ValidateFission
set_option autoImplicit false
namespace NNH_SmallUsize
open Aeneas Aeneas.Std Result

theorem mul : (3#usize * 32#usize : Result Usize)=.ok 96#usize := by
 obtain ⟨r,run,value⟩ := UScalar.mul_spec (x:=3#usize) (y:=32#usize) (by scalar_tac)
 have same : r=96#usize := by
  apply UScalar.eq_of_val_eq
  scalar_tac
 simpa only [same] using run

theorem first : (8#usize + 96#usize : Result Usize)=.ok 104#usize := by
 obtain ⟨r,run,value⟩ := UScalar.add_spec (x:=8#usize) (y:=96#usize) (by scalar_tac)
 have same : r=104#usize := by
  apply UScalar.eq_of_val_eq
  scalar_tac
 simpa only [same] using run

theorem last : (104#usize + 216#usize : Result Usize)=.ok 320#usize := by
 obtain ⟨r,run,value⟩ := UScalar.add_spec (x:=104#usize) (y:=216#usize) (by scalar_tac)
 have same : r=320#usize := by
  apply UScalar.eq_of_val_eq
  scalar_tac
 simpa only [same] using run
#print axioms mul
#print axioms first
#print axioms last
end NNH_SmallUsize
