import NDM_NextGate
set_option autoImplicit false
namespace NDM_GateTotal
open Aeneas Aeneas.Std Result

theorem reference (live next : U64) :
 NDM_GateRef.next_gate_ref live next = ok (decide (live.val+1=next.val)) := by
 by_cases bounded : live.val+1 ≤ U64.max
 · obtain ⟨out,run,meaning⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=live) (y:=1#u64) (by simpa using bounded))
   have call : U64.checked_add live 1#u64=some out := by
    change Option.ofResult (live+1#u64)=some out
    rw [run]
    rfl
   have value : out.val=live.val+1 := by simpa using meaning
   have eqv : out=next ↔ live.val+1=next.val := by
    constructor
    · intro h; simpa only [h] using value.symm
    · intro h; exact UScalar.eq_of_val_eq (value.trans h)
   simp [NDM_GateRef.next_gate_ref,call,lift,eqv]
 · have neq : live.val+1≠next.val := by scalar_tac
   have large : ¬ live.val+1 < 18446744073709551616 := by scalar_tac
   have call : U64.checked_add live 1#u64=none := by
    change Option.ofResult (UScalar.tryMk .U64 (live.val+1))=none
    simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds, large,
      Option.ofResult,ofOption]
   simp [NDM_GateRef.next_gate_ref,call,lift,neq]

#print axioms reference
end NDM_GateTotal
