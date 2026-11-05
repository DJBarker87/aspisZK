import NHJ_SnapshotEntry
import NGL_StorageCases
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace NHJ_EntryDomains
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry AspisR1.S2W_D189Wrappers

theorem source_domain (e : Entry) (a : Nat) (l1 l2 : Usize)
    (first : NGL_StorageCases.Allowed l1) (second : NGL_StorageCases.Allowed l2) :
    NGL_StorageCases.Domain (e.snapshot a l1.val l2.val) := by
  let old := (e.records (e.handles a).1).owned
  apply NGL_StorageCases.source NHJ_StdCopy.copy NHJ_StdCopy.length_law
    old.key old.owner old.is_signer old.is_writable old.executable l1 l2 first second
    (.Ok (e.buffers (e.handles a).1))
  · intro error impossible
    cases impossible
  · exact NHJ_SnapshotEntry.source e a l1 l2

theorem first_table (e : Entry) : ∀ a : Nat,
    NGL_StorageCases.Domain (e.snapshot a (firstSizes a).1 (firstSizes a).2)
  | 0 => source_domain e 0 58295#usize 58295#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 1 => source_domain e 1 1880#usize 1880#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | a+2 => source_domain e (a+2) 1768#usize 1768#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])

theorem second_table (e : Entry) : ∀ a : Nat,
    NGL_StorageCases.Domain (e.snapshot a (secondSizes a).1 (secondSizes a).2)
  | 0 => source_domain e 0 58295#usize 58295#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 1 => source_domain e 1 384#usize 384#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 2 => source_domain e 2 192#usize 192#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 3 => source_domain e 3 768#usize 768#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 4 => source_domain e 4 128#usize 256#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | 5 => source_domain e 5 192#usize 320#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])
  | a+6 => source_domain e (a+6) 1768#usize 1768#usize
      (by simp [NGL_StorageCases.Allowed]) (by simp [NGL_StorageCases.Allowed])

theorem allocation_bounds (n : Usize) (allowed : NGL_StorageCases.Allowed n) :
    0 < n.val ∧ n.val ≤ 58295 := by
  refine ⟨?_,NGL_StorageCases.bounded n allowed⟩
  simp only [NGL_StorageCases.Allowed,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h|h|h|h|h|h|h|h|h <;> omega
#print axioms source_domain
#print axioms first_table
#print axioms second_table
#print axioms allocation_bounds
end NHJ_EntryDomains
