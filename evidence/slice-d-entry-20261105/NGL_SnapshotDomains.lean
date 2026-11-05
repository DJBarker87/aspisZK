import NGL_SnapshotModel
set_option autoImplicit false
noncomputable section
namespace NGL_SnapshotDomains
open Aeneas Aeneas.Std Result NGL_SnapshotModel

theorem consistent (copy : Bytes → Result V) (copyLaw : CopyLengthLaw copy)
    (key owner : Key) (s w e : Bool) (l1 l2 : Usize)
    (borrowed : core.result.Result Bytes PE) (borrowLaw : BorrowErrorLaw borrowed)
    (a : Account) (returned : run copy key owner s w e l1 l2 borrowed = ok a) :
    Consistent a := by
  cases borrowed with
  | Err error =>
    have same := borrowLaw error rfl
    subst error
    simp only [run, Result.ok.injEq] at returned
    subst a
    simp [Consistent]
  | Ok bytes =>
    by_cases admitted : Slice.len bytes = l1 ∨ Slice.len bytes = l2
    · rw [accepted_length copy key owner s w e l1 l2 bytes admitted] at returned
      cases call : copy bytes with
      | fail err => simp only [call,bind_tc_fail] at returned; cases returned
      | div => simp only [call,bind_tc_div] at returned; cases returned
      | ok v =>
        simp only [call,bind_tc_ok,Result.ok.injEq] at returned
        subst a
        have length := copyLaw bytes v call
        simp [Consistent,length]
    · simp only [run,if_neg admitted,Result.ok.injEq] at returned
      subst a
      simp [Consistent]

theorem length_error_domain (a : Account) (valid : Consistent a) :
    ∀ error, a.length = .Err error → NGL_CloneDomain.SnapshotError error := by
  intro error stored
  exact Or.inl (valid.1 error stored)

theorem bytes_error_domain (a : Account) (valid : Consistent a) :
    ∀ error, a.bytes = .Err error → NGL_CloneDomain.SnapshotError error := valid.2.1

theorem checkpoint_bytes_length (a : Account) (valid : Consistent a)
    (v : V) (length : a.length = .Ok 1768#usize) (bytes : a.bytes = .Ok v) :
    v.deref.val.length = 1768 := by
  exact (valid.2.2 1768#usize v length bytes).symm
#print axioms consistent
#print axioms length_error_domain
#print axioms bytes_error_domain
#print axioms checkpoint_bytes_length
end NGL_SnapshotDomains
