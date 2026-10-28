import Init
namespace PV_KStub_AppendDomain
/-- A single symbolic-length append includes the historical fixed-length gate. -/
theorem original_instance (P : Nat → Nat → Prop)
    (symbolic : ∀ n m, n ≤ 2 → m ≤ 1 → P n m) : P 2 1 :=
  symbolic 2 1 (Nat.le_refl _) (Nat.le_refl _)
/-- Empty prefix and tail remain in the strengthened admitted domain. -/
theorem empty_instances (P : Nat → Nat → Prop)
    (symbolic : ∀ n m, n ≤ 2 → m ≤ 1 → P n m) :
    P 0 0 ∧ P 0 1 ∧ P 2 0 :=
  ⟨symbolic 0 0 (Nat.zero_le _) (Nat.zero_le _),
   symbolic 0 1 (Nat.zero_le _) (Nat.le_refl _),
   symbolic 2 0 (Nat.le_refl _) (Nat.zero_le _)⟩
#print axioms original_instance
#print axioms empty_instances
end PV_KStub_AppendDomain
