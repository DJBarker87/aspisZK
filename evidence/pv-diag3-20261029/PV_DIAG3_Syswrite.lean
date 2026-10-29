import PV_DIAG3_Write
/-! Linux std FileDesc::write and cvt. libc::write and errno are external
influence channels under the final input-free ruling; they remain native operations with their
full returned state and effects, never fresh independent simulator coins. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S E : Type}
structure SysWriteOps (S E : Type) where
 readLimit : Nat
 syscall : Nat → Bytes → Nat → Op S Int
 lastError : Op S E
 castUsize : Int → Nat
def cvtWrite (o : SysWriteOps S E) (ret : Int) : Op S (Except E Nat) :=
 if ret = -1 then sequence o.lastError (fun e => pure (.error e))
 else pure (.ok (o.castUsize ret))
def fdWrite (o : SysWriteOps S E) (fd : Nat) (buf : Bytes) : Op S (Except E Nat) :=
 sequence (o.syscall fd buf (min buf.length o.readLimit)) (cvtWrite o)
/-- sys::stdio::Stderr uses ManuallyDrop<FileDesc>; it must not close fd2
when the borrowed temporary ends. No ownership of the descriptor moves. -/
def rawStderrWrite (o : SysWriteOps S E) (buf : Bytes) : Op S (Except E Nat) :=
 fdWrite o 2 buf


theorem syscall_error_reads_errno (o : SysWriteOps S E) :
 cvtWrite o (-1) = sequence o.lastError (fun e => pure (.error e)) := by
 simp [cvtWrite]
#print axioms syscall_error_reads_errno

theorem syscall_success_no_errno (o : SysWriteOps S E) (ret : Int) (h : ret ≠ -1) :
 cvtWrite o ret = pure (.ok (o.castUsize ret)) := by simp [cvtWrite,h]
#print axioms syscall_success_no_errno

theorem fd_write_uses_limit (o : SysWriteOps S E) (fd : Nat) (buf : Bytes) :
 fdWrite o fd buf = sequence (o.syscall fd buf (min buf.length o.readLimit)) (cvtWrite o) := rfl
#print axioms fd_write_uses_limit

theorem stderr_descriptor_exact (o : SysWriteOps S E) (buf : Bytes) :
 rawStderrWrite o buf = fdWrite o 2 buf := rfl
#print axioms stderr_descriptor_exact

theorem fd_write_error_prefix (o : SysWriteOps S E) (fd : Nat) (buf : Bytes)
 (s t : S) (es : List Event)
 (h : o.syscall fd buf (min buf.length o.readLimit) s = ⟨es,t,.value (-1)⟩) :
 fdWrite o fd buf s = prepend es
 (bind (o.lastError t) (fun e => pure (.error e))) := by
 simp [fdWrite,sequence,h,bind,cvtWrite]
#print axioms fd_write_error_prefix

theorem fd_write_success_prefix (o : SysWriteOps S E) (fd : Nat) (buf : Bytes)
 (s t : S) (es : List Event) (ret : Int) (hne : ret ≠ -1)
 (h : o.syscall fd buf (min buf.length o.readLimit) s = ⟨es,t,.value ret⟩) :
 fdWrite o fd buf s = ⟨es,t,.value (.ok (o.castUsize ret))⟩ := by
 simp [fdWrite,sequence,h,bind,cvtWrite,hne,prepend,pure]
#print axioms fd_write_success_prefix

theorem fd_write_abort_no_errno (o : SysWriteOps S E) (fd : Nat) (buf : Bytes)
 (s t : S) (es : List Event) (c : Crash)
 (h : o.syscall fd buf (min buf.length o.readLimit) s = ⟨es,t,.abort c⟩) :
 fdWrite o fd buf s = ⟨es,t,.abort c⟩ := by simp [fdWrite,sequence,h,bind]
#print axioms fd_write_abort_no_errno

theorem fd_write_divergent_prefix (o : SysWriteOps S E) (fd : Nat) (buf : Bytes)
 (s t : S) (es : List Event)
 (h : o.syscall fd buf (min buf.length o.readLimit) s = ⟨es,t,.diverge⟩) :
 fdWrite o fd buf s = ⟨es,t,.diverge⟩ := by simp [fdWrite,sequence,h,bind]
#print axioms fd_write_divergent_prefix
end PV_DIAG3
