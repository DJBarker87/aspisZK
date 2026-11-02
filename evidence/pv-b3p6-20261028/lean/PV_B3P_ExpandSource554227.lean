import PV_B3P_E227_13
import PV_B3P_LinkDefinitions13227
import PV_B3P_ExpandCallerBounds15227
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow
set_option autoImplicit false

def expand_reverse_step554 {N : Usize} (prepared : host_terminal_field.PreparedQm31Multiplier)
    (weights : Array aspis_core.field.QM31 N) (finish : Usize) :
    Result (ControlFlow (Array aspis_core.field.QM31 N × Usize) (Array aspis_core.field.QM31 N)) := do
  if finish > 0#usize then
    let index ← lift (Usize.wrapping_sub finish 1#usize)
    let parent ← Array.index_usize weights index
    let right ← host_terminal_field.PreparedQm31Multiplier.mul prepared parent
    let left ← aspis_core.field.QM31.sub parent right
    let even ← lift (Usize.wrapping_mul 2#usize index)
    let weights1 ← Array.update weights even left
    let twice ← lift (Usize.wrapping_mul 2#usize index)
    let odd ← lift (Usize.wrapping_add twice 1#usize)
    let weights2 ← Array.update weights1 odd right
    .ok (cont (weights2,index))
  else .ok (done weights)

theorem expand_reverse_step_reference554 {N : Usize}
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (weights : Array aspis_core.field.QM31 N) (finish : Usize) :
    expand_reverse_step554 prepared weights finish =
      reference_copy_terminal.Selectors.expand_loop0_loop0.body prepared weights finish := by
  unfold expand_reverse_step554 reference_copy_terminal.Selectors.expand_loop0_loop0.body
  rfl

def expand_reverse554 {N : Usize} (weights : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier) (finish : Usize) :
    Result (Array aspis_core.field.QM31 N) :=
  loop (fun (w,i) => expand_reverse_step554 prepared w i) (weights,finish)

theorem expand_reverse_reference554 {N : Usize} (weights : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier) (finish : Usize) :
    expand_reverse554 weights prepared finish =
      reference_copy_terminal.Selectors.expand_loop0_loop0 weights prepared finish := by
  unfold expand_reverse554 reference_copy_terminal.Selectors.expand_loop0_loop0
  simp only [expand_reverse_step_reference554]

def expand_coordinate_step554 {N : Usize} (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) (weights : Array aspis_core.field.QM31 N) (len coordinate : Usize) :
    Result (ControlFlow (Array aspis_core.field.QM31 N × Usize × Usize) (Array aspis_core.field.QM31 N)) := do
  let stop ← lift (Usize.wrapping_add start count)
  if coordinate < stop then
    let value ← Array.index_usize point coordinate
    let prepared ← host_terminal_field.PreparedQm31Multiplier.new value
    let next ← expand_reverse554 weights prepared len
    let len1 ← lift (Usize.wrapping_mul len 2#usize)
    let coordinate1 ← lift (Usize.wrapping_add coordinate 1#usize)
    .ok (cont (next,len1,coordinate1))
  else .ok (done weights)

theorem expand_coordinate_step_reference554 {N : Usize}
    (point : Array aspis_core.field.QM31 10#usize) (start count : Usize)
    (weights : Array aspis_core.field.QM31 N) (len coordinate : Usize) :
    expand_coordinate_step554 point start count weights len coordinate =
      reference_copy_terminal.Selectors.expand_loop0.body point start count weights len coordinate := by
  unfold expand_coordinate_step554 reference_copy_terminal.Selectors.expand_loop0.body
  simp only [expand_reverse_reference554]

def expand_coordinates554 {N : Usize} (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) (weights : Array aspis_core.field.QM31 N) (len coordinate : Usize) :
    Result (Array aspis_core.field.QM31 N) :=
  loop (fun (w,l,c) => expand_coordinate_step554 point start count w l c) (weights,len,coordinate)

theorem expand_coordinates_reference554 {N : Usize}
    (point : Array aspis_core.field.QM31 10#usize) (start count : Usize)
    (weights : Array aspis_core.field.QM31 N) (len coordinate : Usize) :
    expand_coordinates554 point start count weights len coordinate =
      reference_copy_terminal.Selectors.expand_loop0 point start count weights len coordinate := by
  unfold expand_coordinates554 reference_copy_terminal.Selectors.expand_loop0
  simp only [expand_coordinate_step_reference554]

/-- Point-index representation of the two checked actual slices. The Rust
slice adapter and its fixed bounds are recorded separately in the source dossier. -/
def expand_source554 (N : Usize) (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) : Result (Array aspis_core.field.QM31 N) := do
  let weights := Array.repeat N aspis_core.field.QM31.ZERO
  let initial ← Array.update weights 0#usize aspis_core.field.QM31.ONE
  expand_coordinates554 point start count initial 1#usize start

theorem expand_source_reference554 (N : Usize) (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) :
    expand_source554 N point start count = reference_copy_terminal.Selectors.expand N point start count := by
  unfold expand_source554 reference_copy_terminal.Selectors.expand
  simp only [expand_coordinates_reference554]

theorem expand_source_link554 : PV_B3P_Links13227.PV_B3P_Link_poseidon_expand expand_source554 :=
  funext fun N => funext fun point => funext fun start => funext (expand_source_reference554 N point start)

#print axioms expand_reverse_step_reference554
#print axioms expand_reverse_reference554
#print axioms expand_coordinate_step_reference554
#print axioms expand_coordinates_reference554
#print axioms expand_source_reference554
#print axioms expand_source_link554
end PV_B3P_Association554227
