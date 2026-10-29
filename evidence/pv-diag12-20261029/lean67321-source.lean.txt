import PV_DIAG12_Boundary
namespace PV_DIAG12
set_option autoImplicit false

def linuxReadLimit : Nat := 9223372036854775807
def fdWrite (fd : Int) (s : Span) (r : Reply) : Exec Nat :=
 call (.write fd s (min s.bytes.length linuxReadLimit)) r
def fdFlush : Exec Unit := pureE ()
/- OwnedFd::drop ignores close's result, without retry or cvt/errno read.
A cut is still a missing return, not ordinary completion. -/
def fdDrop (fd : Int) (r : Reply) : Exec Unit :=
 ⟨[⟨.close fd,r⟩],match r with | .cut => .cut | _ => .ok ()⟩
theorem fd_write_request (fd : Int) (s : Span) (r : Reply) :
 requested (fdWrite fd s r).trace=[.write fd s (min s.bytes.length linuxReadLimit)] := rfl
#print axioms fd_write_request

theorem fd_write_count_bounded (fd : Int) (s : Span) (r : Reply) :
 (fdWrite fd s r).trace=[⟨.write fd s (min s.bytes.length linuxReadLimit),r⟩] := rfl
theorem fd_flush_no_fsync : fdFlush=⟨[],.ok ()⟩ := rfl
#print axioms fd_write_count_bounded
#print axioms fd_flush_no_fsync

theorem fd_drop_error_not_retried (fd e : Int) :
 fdDrop fd (.error e)=⟨[⟨.close fd,.error e⟩],.ok ()⟩ := rfl
theorem fd_drop_success (fd : Int) (n : Nat) :
 fdDrop fd (.returned n)=⟨[⟨.close fd,.returned n⟩],.ok ()⟩ := rfl
#print axioms fd_drop_error_not_retried
#print axioms fd_drop_success

def maskBadFd {A : Type} (fallback : A) (r : Exec A) : Exec A :=
 ⟨r.trace,match r.result with | .error e => if e=9 then .ok fallback else .error e | x => x⟩
def stdWrite (fd : Int) (s : Span) (r : Reply) : Exec Nat :=
 maskBadFd s.bytes.length (fdWrite fd s r)
theorem mask_preserves_requests {A : Type} (a : A) (r : Exec A) :
 (maskBadFd a r).trace=r.trace := rfl
#print axioms mask_preserves_requests

theorem std_ebadf_accepted (fd : Int) (s : Span) :
 (stdWrite fd s (.error 9)).result=.ok s.bytes.length := by
 simp only [stdWrite,maskBadFd,fdWrite,call,eq_self,ite_true]
theorem std_ebadf_not_delivered (fd : Int) (s : Span) :
 delivered fd (stdWrite fd s (.error 9)).trace=[] := rfl
#print axioms std_ebadf_accepted
#print axioms std_ebadf_not_delivered

theorem std_other_error (fd e : Int) (s : Span) (h : e≠9) :
 (stdWrite fd s (.error e)).result=.error e := by
 simp only [stdWrite,maskBadFd,fdWrite,call,if_neg h]
theorem std_write_success (fd : Int) (s : Span) (n : Nat) :
 (stdWrite fd s (.returned n)).result=.ok n := rfl
#print axioms std_other_error
#print axioms std_write_success

theorem std_cut (fd : Int) (s : Span) :
 (stdWrite fd s .cut).result=.cut := rfl
theorem std_write_trace (fd : Int) (s : Span) (r : Reply) :
 (stdWrite fd s r).trace=(fdWrite fd s r).trace := rfl
#print axioms std_cut
#print axioms std_write_trace

def stdoutWrite := stdWrite 1
def stderrWrite := stdWrite 2
theorem stdout_request (s : Span) (r : Reply) :
 requested (stdoutWrite s r).trace=[.write 1 s (min s.bytes.length linuxReadLimit)] := rfl
theorem stderr_request (s : Span) (r : Reply) :
 requested (stderrWrite s r).trace=[.write 2 s (min s.bytes.length linuxReadLimit)] := rfl
#print axioms stdout_request
#print axioms stderr_request

theorem fd_drop_cut (fd : Int) :
 fdDrop fd .cut=⟨[⟨.close fd,.cut⟩],.cut⟩ := rfl
theorem no_close_stdout (s : Span) (r : Reply) :
 ∀ e ∈ (stdoutWrite s r).trace, e.request≠.close 1 := by
 intro e h; simp only [stdoutWrite,stdWrite,maskBadFd,fdWrite,call,List.mem_singleton] at h
 cases h; intro h; cases h
#print axioms fd_drop_cut
#print axioms no_close_stdout

end PV_DIAG12
