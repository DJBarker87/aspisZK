import PV_B1_PoleInner
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleMiddle
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258 PV_B1_PoleInner
abbrev Mid := all_slots_clear_loop0_loop0

def twoSides (values : Rows) (chi : Q) (clear : Bool) (row : Usize) (active : Bool) : Result Bool := do
  let c ← two values chi clear row active 0#usize
  two values chi c row active 1#usize

theorem source_unfold (values : Rows) (chi : Q) (clear : Bool)
    (row : Usize) (active : Bool) (side : Usize) :
    Mid values chi clear row active side = (do
      let cf ← all_slots_clear_loop0_loop0.body values chi row active clear side
      match cf with
      | .done b => ok b
      | .cont (c,s) => Mid values chi c row active s) := by
  unfold Mid all_slots_clear_loop0_loop0
  rw [PV_B1_Loop.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf hcf
  cases cf with
  | done b => rfl
  | cont pair => rcases pair with ⟨c,s⟩; rfl

theorem stop (values : Rows) (chi : Q) (clear : Bool) (row : Usize) (active : Bool) :
    Mid values chi clear row active 2#usize = ok clear := by
  rw [source_unfold]
  simp only [all_slots_clear_loop0_loop0.body,lt_self_iff_false,if_false,bind_tc_ok]

theorem one (values : Rows) (chi : Q) (clear : Bool) (row : Usize) (active : Bool) :
    Mid values chi clear row active 1#usize = two values chi clear row active 1#usize := by
  rw [source_unfold]
  have hi : (1#usize : Usize)<2#usize := by decide
  have inc : Usize.wrapping_add 1#usize 1#usize = 2#usize := by decide
  simp only [all_slots_clear_loop0_loop0.body,hi,if_true,PV_B1_PoleInner.source,
    lift,bind_tc_ok,bind_assoc_eq,inc,stop]
  cases two values chi clear row active 1#usize <;> rfl

theorem source (values : Rows) (chi : Q) (clear : Bool) (row : Usize) (active : Bool) :
    Mid values chi clear row active 0#usize = twoSides values chi clear row active := by
  rw [source_unfold]
  have hi : (0#usize : Usize)<2#usize := by decide
  have inc : Usize.wrapping_add 0#usize 1#usize = 1#usize := by decide
  simp only [all_slots_clear_loop0_loop0.body,hi,if_true,PV_B1_PoleInner.source,
    lift,bind_tc_ok,bind_assoc_eq,inc,one,twoSides] <;> rfl
#print axioms source_unfold
#print axioms stop
#print axioms one
#print axioms source
end PV_B1_PoleMiddle
