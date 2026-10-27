import PV_B1_PoleLiterals
import PV_B1_PoleKeep
import PV_B1_Loop
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleInner
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258
abbrev Q := aspis_core.field.QM31
abbrev Rows := Slice (Array (Array Q 2#usize) 2#usize)
abbrev Src := all_slots_clear_loop0_loop0_loop0

def read (values : Rows) (row side slot : Usize) : Result Q := do
  let r ← Slice.index_usize values row
  let pair ← Array.index_usize r side
  Array.index_usize pair slot

def two (values : Rows) (chi : Q) (clear : Bool) (row : Usize) (active : Bool) (side : Usize) : Result Bool := do
  let a ← read values row side 0#usize
  let c ← keep_clear clear active chi a
  let b ← read values row side 1#usize
  keep_clear c active chi b

theorem source_unfold (values : Rows) (chi : Q) (clear : Bool)
    (row : Usize) (active : Bool) (side slot : Usize) :
    Src values chi clear row active side slot = (do
      let cf ← all_slots_clear_loop0_loop0_loop0.body values chi row active side clear slot
      match cf with
      | .done b => ok b
      | .cont (c,s) => Src values chi c row active side s) := by
  unfold Src all_slots_clear_loop0_loop0_loop0
  rw [PV_B1_Loop.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf hcf
  cases cf with
  | done b => rfl
  | cont pair => rcases pair with ⟨c,s⟩; rfl

theorem stop (values : Rows) (chi : Q) (clear : Bool)
    (row : Usize) (active : Bool) (side : Usize) :
    Src values chi clear row active side 2#usize = ok clear := by
  rw [source_unfold]
  simp only [all_slots_clear_loop0_loop0_loop0.body,lt_self_iff_false,if_false,bind_tc_ok]

theorem one (values : Rows) (chi : Q) (clear : Bool)
    (row : Usize) (active : Bool) (side : Usize) :
    Src values chi clear row active side 1#usize = (do
      let v ← read values row side 1#usize
      keep_clear clear active chi v) := by
  rw [source_unfold]
  have hi : (1#usize : Usize)<2#usize := by decide
  have inc : Usize.wrapping_add 1#usize 1#usize = 2#usize := PV_B1_PoleLiterals.one
  simp only [all_slots_clear_loop0_loop0_loop0.body,hi,if_true,lift,bind_tc_ok,
    read,bind_assoc_eq,inc,PV_B1_PoleKeep.source,stop] <;> rfl

theorem source (values : Rows) (chi : Q) (clear : Bool)
    (row : Usize) (active : Bool) (side : Usize) :
    Src values chi clear row active side 0#usize = two values chi clear row active side := by
  rw [source_unfold]
  have hi : (0#usize : Usize)<2#usize := by decide
  have inc : Usize.wrapping_add 0#usize 1#usize = 1#usize := PV_B1_PoleLiterals.zero
  simp only [all_slots_clear_loop0_loop0_loop0.body,hi,if_true,lift,bind_tc_ok,
    two,read,bind_assoc_eq,inc,one,PV_B1_PoleKeep.source] <;> rfl
#print axioms source_unfold
#print axioms stop
#print axioms one
#print axioms source
end PV_B1_PoleInner
