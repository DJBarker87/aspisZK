import Aeneas
set_option autoImplicit false
namespace R1Z.PDict_ArrayRead262
open Aeneas Aeneas.Std Result

/-- Generic read equation prevents WP elaboration from inspecting a concrete
List.ofFn allocation at a use site. -/
theorem read {T : Type} {n : Usize} (rows : Array T n) (index : Usize)
    (bound : index.val < rows.length) :
    Array.index_usize rows index = .ok rows[index] := by
  obtain ⟨value,run,atIndex⟩ := WP.spec_imp_exists (Array.index_usize_spec rows index bound)
  rw [atIndex] at run
  exact run

#print axioms read
end R1Z.PDict_ArrayRead262
