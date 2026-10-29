import R1Z.PV_RunJoin_WeightFactorRestore47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightFiveSet47
open Aeneas Aeneas.Std

theorem shape {A : Type} (a : Array A 5#usize) :
    ∃ a0 a1 a2 a3 a4, a=Array.make 5#usize [a0,a1,a2,a3,a4] := by
  rcases a with ⟨xs,h⟩
  change xs.length=5 at h
  match xs with
  | [a0,a1,a2,a3,a4] => exact ⟨a0,a1,a2,a3,a4,rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | _::_::_::_::_::_::_ =>
    simp only [List.length_cons,List.length_nil] at h;omega
#print axioms shape

theorem complete {A : Type} (a : Array A 5#usize) (a0 a1 a2 a3 a4 : A) :
    Aeneas.Std.Array.set (Aeneas.Std.Array.set (Aeneas.Std.Array.set
      (Aeneas.Std.Array.set (Aeneas.Std.Array.set a 0#usize a0) 1#usize a1) 2#usize a2)
        3#usize a3) 4#usize a4=Array.make 5#usize [a0,a1,a2,a3,a4] := by
  obtain ⟨b0,b1,b2,b3,b4,he⟩ := shape a
  subst a
  apply Subtype.ext
  simp only [Aeneas.Std.Array.set,Array.make,
    show (0#usize).val=0 from by scalar_tac,show (1#usize).val=1 from by scalar_tac,
    show (2#usize).val=2 from by scalar_tac,show (3#usize).val=3 from by scalar_tac,
    show (4#usize).val=4 from by scalar_tac,List.set]
#print axioms complete
end R1Z.PV_RunJoin_WeightFiveSet47
