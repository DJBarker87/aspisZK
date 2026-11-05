import NGL_SnapshotCases
set_option autoImplicit false
noncomputable section
namespace NGL_StorageCases
open Aeneas Aeneas.Std Result NGL_SnapshotModel

def Allowed (n : Usize) : Prop := n.val ∈ [58295,1768,1880,384,192,768,128,256,320]

theorem bounded (n : Usize) (allowed : Allowed n) : n.val ≤ 58295 := by
  simp only [Allowed,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h|h|h|h|h|h|h|h|h <;> omega

theorem copied_selected (copy : Bytes → Result V) (key owner : Key) (s w e : Bool)
    (l1 l2 : Usize) (borrowed : core.result.Result Bytes PE) (a : Account)
    (returned : run copy key owner s w e l1 l2 borrowed = ok a)
    (n : Usize) (v : V) (hl : a.length = .Ok n) (hb : a.bytes = .Ok v) : n=l1 ∨ n=l2 := by
  cases borrowed with
  | Err error =>
    simp only [run,Result.ok.injEq] at returned
    subst a
    cases hl
  | Ok bytes =>
    by_cases admitted : Slice.len bytes = l1 ∨ Slice.len bytes = l2
    · rw [accepted_length copy key owner s w e l1 l2 bytes admitted] at returned
      cases call : copy bytes with
      | fail err => simp only [call,bind_tc_fail] at returned; cases returned
      | div => simp only [call,bind_tc_div] at returned; cases returned
      | ok value =>
        simp only [call,bind_tc_ok,Result.ok.injEq] at returned
        subst a
        have same : Slice.len bytes = n := core.result.Result.Ok.inj hl
        rw [← same]
        exact admitted
    · simp only [run,if_neg admitted,Result.ok.injEq] at returned
      subst a
      cases hb

def Domain (a : Account) : Prop := NGL_SnapshotCases.Domain a ∧
  ∀ n v, a.length = .Ok n → a.bytes = .Ok v → Allowed n

theorem source (copy : Bytes → Result V) (copyLaw : CopyLengthLaw copy)
    (key owner : Key) (s w e : Bool) (l1 l2 : Usize)
    (first : Allowed l1) (second : Allowed l2)
    (borrowed : core.result.Result Bytes PE) (borrowLaw : BorrowErrorLaw borrowed)
    (a : Account) (returned : run copy key owner s w e l1 l2 borrowed = ok a) : Domain a := by
  refine ⟨NGL_SnapshotCases.source_domain copy copyLaw key owner s w e l1 l2
    (bounded l1 first) (bounded l2 second) borrowed borrowLaw a returned,?_⟩
  intro n v hl hb
  rcases copied_selected copy key owner s w e l1 l2 borrowed a returned n v hl hb with h|h
  · simpa only [h] using first
  · simpa only [h] using second
#print axioms bounded
#print axioms copied_selected
#print axioms source
end NGL_StorageCases
