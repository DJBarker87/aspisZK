import NMX_OwnedPackets
set_option autoImplicit false
namespace NMX_OwnershipLaws
open Aeneas Aeneas.Std NMX_OwnedPackets
/-- The full successful carrier admits exactly the four owners supplied by
its four source allocation occurrences, retaining each complete payload. -/
theorem exact_owners (mk ck lk : Array U8 32#usize) (m : Box Master)
 (c : Box Checkpoint) (l : Box Lane) (s : Box Snapshot) :
 (Auth.mk mk ck lk m c l s).owners = [m.owner,c.owner,l.owner,s.owner] := rfl

theorem freshness (mk ck lk : Array U8 32#usize) (m : Box Master)
 (c : Box Checkpoint) (l : Box Lane) (s : Box Snapshot) (prior : List Nat)
 (distinct : [m.owner,c.owner,l.owner,s.owner].Nodup)
 (newOwners : ∀ o ∈ [m.owner,c.owner,l.owner,s.owner], o ∉ prior) :
 (Auth.mk mk ck lk m c l s).Fresh prior := ⟨distinct,newOwners⟩
/-- A payload-only equality does not imply owner equality. Therefore none of
the source value links can be substituted for the full RowSpec233. -/
theorem owner_not_erased (a : Auth) (owner : Nat) (different : owner ≠ a.master.owner) :
 ({a with master := ⟨owner,a.master.payload⟩} : Auth).erase = a.erase ∧
 ({a with master := ⟨owner,a.master.payload⟩} : Auth) ≠ a := by
 constructor
 · rfl
 · intro h
   have same := congrArg (fun b : Auth => b.master.owner) h
   exact different same
#print axioms exact_owners
#print axioms freshness
#print axioms owner_not_erased
end NMX_OwnershipLaws
