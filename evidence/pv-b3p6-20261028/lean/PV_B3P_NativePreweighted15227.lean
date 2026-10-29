import PV_B3P_PreweightedMacro12227
import PV_B3P_Operations12227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

/-- The source macro executes all four lane slots before the packed read,
pack call, addition and write. Empty and invalid spans keep their Result. -/
def native_preweighted15 {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (start : Usize) (values : Array aspis_core.field.QM31 N) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let first ← start / 4#usize
  let stop ← lift (Usize.wrapping_add start N)
  let before ← lift (Usize.wrapping_sub stop 1#usize)
  let last ← before / 4#usize
  loop (inclusive_body12 (source_preweighted_macro_step12 start values) last) (packed,first)

theorem native_preweighted_binding15 : @native_preweighted15 = @reference_terminal.add_preweighted := by
  have steps : ∀ (N : Usize) (start : Usize) (values : Array aspis_core.field.QM31 N),
      source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    intro N start values
    funext packed group
    exact preweighted_macro_step_binding12 start values packed group
  funext N packed start values
  unfold native_preweighted15
  rw [steps]
  exact (congrFun (congrFun (congrFun (congrFun preweighted_operation_binding12 N) packed) start) values).symm
#print axioms native_preweighted_binding15
end PV_B3P_Native15227
