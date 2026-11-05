import NGL_SnapshotDomains
import NGL_LengthCarrier
set_option autoImplicit false
noncomputable section
namespace NGL_SnapshotCases
open Aeneas Aeneas.Std Result NGL_SnapshotModel

def Domain (a : Account) : Prop :=
  (a.length = .Err .AccountBorrowFailed ∧ a.bytes = .Err .AccountBorrowFailed) ∨
  (∃ n, a.length = .Ok n ∧ a.bytes = .Err .InvalidAccountData) ∨
  (∃ n v, a.length = .Ok n ∧ a.bytes = .Ok v ∧
    n.val = v.deref.val.length ∧ n.val ≤ 58295)

theorem source_domain (copy : Bytes → Result V) (copyLaw : CopyLengthLaw copy)
    (key owner : Key) (s w e : Bool) (l1 l2 : Usize)
    (bound1 : l1.val ≤ 58295) (bound2 : l2.val ≤ 58295)
    (borrowed : core.result.Result Bytes PE) (borrowLaw : BorrowErrorLaw borrowed)
    (a : Account) (returned : run copy key owner s w e l1 l2 borrowed = ok a) : Domain a := by
  cases borrowed with
  | Err error =>
    have same := borrowLaw error rfl
    subst error
    simp only [run,Result.ok.injEq] at returned
    subst a
    exact Or.inl ⟨rfl,rfl⟩
  | Ok bytes =>
    by_cases admitted : Slice.len bytes = l1 ∨ Slice.len bytes = l2
    · rw [accepted_length copy key owner s w e l1 l2 bytes admitted] at returned
      cases call : copy bytes with
      | fail err => simp only [call,bind_tc_fail] at returned; cases returned
      | div => simp only [call,bind_tc_div] at returned; cases returned
      | ok v =>
        simp only [call,bind_tc_ok,Result.ok.injEq] at returned
        subst a
        refine Or.inr (Or.inr ⟨Slice.len bytes,v,rfl,rfl,?_,?_⟩)
        · exact (copyLaw bytes v call).symm
        · rcases admitted with h | h
          · simpa only [h] using bound1
          · simpa only [h] using bound2
    · simp only [run,if_neg admitted,Result.ok.injEq] at returned
      subst a
      exact Or.inr (Or.inl ⟨Slice.len bytes,rfl,rfl⟩)

theorem length_domain (a : Account) (valid : Domain a) : NGL_LengthCarrier.domain a.length := by
  rcases valid with ⟨hl,hb⟩ | ⟨n,hl,hb⟩ | ⟨n,v,hl,hb,hn,hbound⟩
  · exact Or.inr (Or.inl hl)
  · exact Or.inl ⟨n,hl⟩
  · exact Or.inl ⟨n,hl⟩
#print axioms source_domain
#print axioms length_domain
end NGL_SnapshotCases
