import PV_DIAG4_ReprDrop
/-! sys::io::is_interrupted takes the stored error code, not fresh errno.
This binds the OS-error arm of write_all's guard and destruction. The syscall
and the returned code's distribution remain external operations. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S A C : Type}
def osInterrupted (code : Fin (2^32)) : Op S Bool :=
 PV_DIAG3.pure (code.val == 4)
def osErrorAfterWrite (code : Fin (2^32)) (drop : C → Op S Unit)
 (retry : Op S (Except (Fin (2^32)) Unit)) : Op S (Except (Fin (2^32)) Unit) :=
 sequence (osInterrupted code) (fun interrupted =>
 if interrupted then sequence (errorReprDrop drop (.os code)) (fun _ => retry)
 else PV_DIAG3.pure (.error code))
theorem os_interrupted_exact (code : Fin (2^32)) (s : S) :
 osInterrupted code s = ⟨[],s,.value (code.val == 4)⟩ := rfl
#print axioms os_interrupted_exact
theorem os_interrupted_no_effect (code : Fin (2^32)) (s : S) :
 (osInterrupted code s).events = [] ∧ (osInterrupted code s).state = s := ⟨rfl,rfl⟩
#print axioms os_interrupted_no_effect
theorem interrupted_drop_then_retry (code : Fin (2^32)) (h : code.val = 4)
 (drop : C → Op S Unit) (retry : Op S (Except (Fin (2^32)) Unit)) :
 osErrorAfterWrite code drop retry = retry := by
 funext s
 simp [osErrorAfterWrite,osInterrupted,h,sequence,PV_DIAG3.pure,PV_DIAG3.bind,errorReprDrop,prepend]
#print axioms interrupted_drop_then_retry
theorem noninterrupted_moves_error (code : Fin (2^32)) (h : code.val ≠ 4)
 (drop : C → Op S Unit) (retry : Op S (Except (Fin (2^32)) Unit)) :
 osErrorAfterWrite code drop retry = PV_DIAG3.pure (.error code) := by
 funext s
 simp [osErrorAfterWrite,osInterrupted,h,sequence,PV_DIAG3.pure,PV_DIAG3.bind,prepend]
#print axioms noninterrupted_moves_error
theorem interrupted_keeps_retry_prefix (code : Fin (2^32)) (h : code.val = 4)
 (drop : C → Op S Unit) (retry : Op S (Except (Fin (2^32)) Unit)) (s : S) :
 osErrorAfterWrite code drop retry s = retry s := by
 rw [interrupted_drop_then_retry code h]
#print axioms interrupted_keeps_retry_prefix
end PV_DIAG4
