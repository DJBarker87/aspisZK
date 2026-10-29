import NDM_GateRef.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDM_NextGate
open Aeneas Aeneas.Std Result

theorem exact_next (live next : U64) (step : next.val=live.val+1) :
 NDM_GateRef.next_gate_ref live next=ok true := by
 obtain ⟨out,run,meaning⟩ := WP.spec_imp_exists
  (UScalar.add_spec (x:=live) (y:=1#u64) (by scalar_tac))
 have same : out=next := by scalar_tac
 have call : U64.checked_add live 1#u64=some next := by
  change Option.ofResult (live+1#u64)=some next
  rw [run,same]
  rfl
 simp [NDM_GateRef.next_gate_ref,call,lift]

#print axioms exact_next
#print Aeneas.Std.UScalar.tryMk
end NDM_NextGate
