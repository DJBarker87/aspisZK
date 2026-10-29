import R1Z.PV_ROWS10B_ControlWord
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Retry
open Aeneas Aeneas.Std PV_ROWS10B_Consumed PV_ROWS10B_ControlWord
/-- Symbolic finite-prefix proof, before any infinite execution is claimed. -/
theorem retry_prefix (indices : List Nat) (n : Nat) :
    run (indices.map (fun _ => (⟨-1,4⟩ : SysWord))) (n+1) = .pending (n+1) := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    change run (is.map (fun _ => (⟨-1,4⟩ : SysWord))) (n+1) = .pending (n+1)
    exact ih

/-- An actual infinite EINTR word diverges in the control model. A truncated
word has never been substituted for this universally quantified premise. -/
theorem perpetual_eintr : Diverges (fun _ => ⟨-1,4⟩) 64 := by
  intro fuel
  exact ⟨64, retry_prefix (List.range fuel) 63⟩

theorem positive_errno_negation_safe (errno : Int)
    (positive : 0 < errno) (bound : errno ≤ 2147483647) :
    -2147483648 ≤ -errno ∧ -errno < 0 := by omega

theorem fd_ready (fd : Int) (nonnegative : 0 ≤ fd) :
    fdEntry fd = .use fd ∧ fdLock fd = .use fd := by
  have h1 : fd ≠ -1 := by omega
  have h2 : fd ≠ -2 := by omega
  simp only [fdEntry, fdLock, h1, h2, or_self, if_false, and_self]

variable {E : Type}
theorem fill_os_error (backend : Op E) (s after : Slice U8) (e : E)
    (nonempty : s.val.length ≠ 0) (reply : backend s = .ok (.Err e, after)) :
    fill backend s = .ok (.Err e, after) := by
  simp only [fill, if_neg nonempty, reply]

theorem fill_abort (backend : Op E) (s : Slice U8) (e : Aeneas.Std.Error)
    (nonempty : s.val.length ≠ 0) (reply : backend s = .fail e) :
    fill backend s = .fail e := by
  simp only [fill, if_neg nonempty, reply]

theorem fill_diverges (backend : Op E) (s : Slice U8)
    (nonempty : s.val.length ≠ 0) (reply : backend s = .div) :
    fill backend s = .div := by
  simp only [fill, if_neg nonempty, reply]

#print axioms retry_prefix
#print axioms perpetual_eintr
#print axioms positive_errno_negation_safe
#print axioms fd_ready
#print axioms fill_os_error
#print axioms fill_abort
#print axioms fill_diverges
end R1Z.PV_ROWS10B_Retry
