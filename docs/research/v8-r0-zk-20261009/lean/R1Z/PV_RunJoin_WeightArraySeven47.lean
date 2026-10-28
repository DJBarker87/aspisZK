import R1Z.PV_RunJoin_WeightCellIndices46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightArraySeven47
open Aeneas Aeneas.Std Result

theorem shape {A : Type} (a : Array A 7#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6, a=Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6] := by
  rcases a with ⟨xs,h⟩
  change xs.length=7 at h
  match xs with
  | [a0,a1,a2,a3,a4,a5,a6] => exact ⟨a0,a1,a2,a3,a4,a5,a6,rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_]
    | _::_::_::_::_::_::_::_::_ => simp only [List.length_cons,List.length_nil] at h;omega
#print axioms shape
end R1Z.PV_RunJoin_WeightArraySeven47
