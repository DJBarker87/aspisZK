import NLQ_DispatchState
set_option autoImplicit false
namespace NLQ_ByteDispatch
open Aeneas Aeneas.Std
/-- Only tiny literal tag discrimination; no large finite enumeration. -/
theorem three {T : Type} (four five six other : T) :
 (match (3#u8 : U8) with
 | 4#uscalar => four
 | 5#uscalar => five
 | 6#uscalar => six
 | _ => other)=other := by
 split
 all_goals trace_state
 all_goals first | contradiction | rfl | simp_all
#print axioms three
end NLQ_ByteDispatch
