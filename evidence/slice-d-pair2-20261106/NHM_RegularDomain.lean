import NHM_RegularKinds
set_option autoImplicit false
namespace NHM_RegularDomain
open Aeneas Aeneas.Std

theorem membership (shared : Bool) (k : Usize) (member : k∈NHM_RegularKinds.kinds shared) :
 k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=5 ∨ k.val=6 := by
 have same : (NHM_RegularKinds.kinds shared).map (fun x : Usize=>x.val)=
  if shared then [2,5,6] else [1,2,3,5,6] := by cases shared <;> rfl
 have hm : k.val∈(NHM_RegularKinds.kinds shared).map (fun x : Usize=>x.val) := List.mem_map.mpr ⟨k,member,rfl⟩
 rw [same] at hm
 cases shared <;> simp at hm <;> omega

theorem child_domain (shared : Bool) (k : Usize) (member : k∈NHM_RegularKinds.kinds shared) :
 NHI_KindDomain.row k.val<5 ∧ k.val<7 :=
 NHI_KindDomain.selected k.val (membership shared k member)

#print axioms membership
#print axioms child_domain
end NHM_RegularDomain
