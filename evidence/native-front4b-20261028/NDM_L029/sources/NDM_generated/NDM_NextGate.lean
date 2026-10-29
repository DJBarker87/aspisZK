import NDM_GateRef.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDM_NextGate
open Aeneas Aeneas.Std Result

theorem exact_next (live next : U64) (step : next.val=live.val+1) :
 NDM_GateRef.next_gate_ref live next=ok true := by
 have call : U64.checked_add live 1#u64=some next :=
  AdapterRw.Scalar.checked_add_eq _ _ _ (by simpa using step)
 simp [NDM_GateRef.next_gate_ref,call,lift]

#print axioms exact_next
#print Aeneas.Std.UScalar.add
#print Aeneas.Std.Option.ofResult
end NDM_NextGate
