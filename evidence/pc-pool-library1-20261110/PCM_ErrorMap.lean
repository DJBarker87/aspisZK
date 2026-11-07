import PCM_Semantics
set_option autoImplicit false
namespace PCM.Computation
open RSL
/-- Rust map_err preserves every event and state on every returned arm and
preserves the exact stopped prefix; the input error is moved, never cloned. -/
def mapError {A : Type} (f : ProgramError → ProgramError) (m : Computation A) : Computation A :=
  fun s env o => ∃ ro, m s env ro ∧ o = ⟨(match ro.exit with
    | .ret (.ok a,s1) => .ret (.ok a,s1)
    | .ret (.error e,s1) => .ret (.error (f e),s1)
    | .abort => .abort | .diverge => .diverge),ro.events⟩
end PCM.Computation
