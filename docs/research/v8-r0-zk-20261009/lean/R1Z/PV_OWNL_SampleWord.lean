import R1Z.PV_OWNK_TowerCanon
set_option autoImplicit false
namespace R1Z.PV_OWNL_SampleWord
open Aeneas Aeneas.Std
/-- Explicit wrapping constructors: no elaborator-generated bound proofs. -/
def u32 (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩
def u64 (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩
def dividend (remainder : U64) (word : U32) : U64 :=
 u64 (remainder.val * 4294967296 + word.val)
def rem64 (n : U64) : U64 := u64 (n.val % 2147483647)
def quotient (n : U64) : U32 := u32 (n.val / 2147483647)
def truncate (n : U64) : U32 := u32 n.val

theorem rem_bound (n : U64) : (rem64 n).val < 2147483647 := by
 have h : n.val % 2147483647 < 2147483647 := Nat.mod_lt _ (by omega)
 change (n.val % 2147483647) % 18446744073709551616 < 2147483647
 rw [Nat.mod_eq_of_lt (by omega)]
 exact h

theorem truncate_canonical (n : U64) (h : n.val < 2147483647) :
 PV_OWNK_ScalarOps.Canon (truncate n) := by
 change n.val % 4294967296 < 2147483647
 rw [Nat.mod_eq_of_lt (by omega)]
 exact h
#print axioms rem_bound
#print axioms truncate_canonical
end R1Z.PV_OWNL_SampleWord
