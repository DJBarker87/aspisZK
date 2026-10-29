import PV_RJ4IDB_DiagWorld
import PV_DIAG3_Syswrite
set_option autoImplicit false
namespace PV_RJ4IDB
variable {S E : Type}
/-- The existing source model passes fd2 and the bounded request to the
syscall. Errno, partial delivery and abnormal terminal remain native leaves. -/
theorem stderr_source (o : PV_DIAG3.SysWriteOps S E) (bytes : Bytes) :
 PV_DIAG3.rawStderrWrite o bytes = PV_DIAG3.sequence
 (o.syscall 2 bytes (min bytes.length o.readLimit)) (PV_DIAG3.cvtWrite o) := rfl

theorem stderr_abort_prefix (expose : S → List (Bytes × Bytes))
 (o : PV_DIAG3.SysWriteOps S E) (bytes : Bytes) (s t : S)
 (es : List PV_DIAG3.Event) (c : PV_DIAG3.Crash)
 (leaf : o.syscall 2 bytes (min bytes.length o.readLimit) s = ⟨es,t,.abort c⟩) :
 diagWithState expose (PV_DIAG3.rawStderrWrite o bytes s) =
 diagWithState expose (⟨es,t,.abort c⟩ : PV_DIAG3.Execution S (Except E Nat)) := by
 unfold PV_DIAG3.rawStderrWrite
 rw [PV_DIAG3.fd_write_abort_no_errno o 2 bytes s t es c leaf]

theorem stderr_divergent_prefix (expose : S → List (Bytes × Bytes))
 (o : PV_DIAG3.SysWriteOps S E) (bytes : Bytes) (s t : S)
 (es : List PV_DIAG3.Event)
 (leaf : o.syscall 2 bytes (min bytes.length o.readLimit) s = ⟨es,t,.diverge⟩) :
 diagWithState expose (PV_DIAG3.rawStderrWrite o bytes s) =
 diagWithState expose (⟨es,t,.diverge⟩ : PV_DIAG3.Execution S (Except E Nat)) := by
 unfold PV_DIAG3.rawStderrWrite
 rw [PV_DIAG3.fd_write_divergent_prefix o 2 bytes s t es leaf]
#print axioms stderr_source
#print axioms stderr_abort_prefix
#print axioms stderr_divergent_prefix
end PV_RJ4IDB
