import PV_B3P_PreweightedStep12227
import PV_B3P_IndexSteps9227
import PV_B3P_UsizeLoop9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

def window_store12 {α : Type} (read : Usize → Result α)
    (output : Array α 4#usize) (slot : Usize) : Result (Array α 4#usize) := do
  let value ← read slot
  Array.update output slot value

def source_four_loop12 {α : Type} (zero : α) (read : Usize → Result α) :
    Result (Array α 4#usize) :=
  loop (usize_body (window_store12 read) 4#usize) (Array.repeat 4#usize zero,0#usize)

theorem source_four_loop_binding12 {α : Type} (zero : α) (read : Usize → Result α) :
    source_four_loop12 zero read = four_build12 read := by
  unfold source_four_loop12
  rw [usize_loop_plan (window_store12 read) 4#usize 0#usize 4 _ (by scalar_tac)]
  have h01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
  have h12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := next_exact _ _ rfl
  have h23 : Usize.wrapping_add 2#usize 1#usize = 3#usize := next_exact _ _ rfl
  simpa only [usize_plan,window_store12,h01,h12,h23,PV_B3P_Ordered227.bind_assoc,
    bind_tc_ok,bind_return12] using four_interleaved12 zero read

def source_preweighted_macro_step12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (packed : Array aspis_core.field.QM31 24#usize) (group : Usize) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let lanes ← source_four_loop12 aspis_core.field.QM31.ZERO (preweighted_window12 start values group)
  let old ← Array.index_usize packed group
  let slice ← lift (Array.to_slice lanes)
  let value ← host_terminal_field.qm31_pack_base4 slice
  let next ← aspis_core.field.QM31.add old value
  Array.update packed group next

theorem preweighted_macro_step_binding12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (packed : Array aspis_core.field.QM31 24#usize) (group : Usize) :
    source_preweighted_macro_step12 start values packed group =
      preweighted_source_step12 start values packed group := by
  unfold source_preweighted_macro_step12 preweighted_source_step12
  rw [source_four_loop_binding12]

#print axioms source_four_loop_binding12
#print axioms preweighted_macro_step_binding12
end PV_B3P_Binding12227
