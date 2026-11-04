import NBH_Exact
set_option autoImplicit false
namespace NEX_Exact
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
/-- The inherited total value law supplies complete Result semantics. The new
native evidence is scoped to widths 8/32 and live slices of length at most 33. -/
theorem result_state_effects {State : Type} (n : Usize) (bytes : Slice U8) (state : State) :
    (pool_v1.pair_terminal.exact n bytes,state,([] : List Unit)) =
    (ok (NBH_Exact.result n bytes),state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit))) (NBH_Exact.source n bytes)
#print axioms result_state_effects
#print axioms NBH_Exact.accepted_bytes
#print axioms NBH_Exact.rejected
end NEX_Exact
