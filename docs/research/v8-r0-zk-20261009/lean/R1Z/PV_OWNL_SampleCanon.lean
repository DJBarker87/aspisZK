import R1Z.PV_OWNK_TowerCanon
set_option autoImplicit false
namespace R1Z.PV_OWNL_SampleCanon
open Aeneas Aeneas.Std PV_OWNK_TowerCanon
/-- u64 shift/OR dividend. Canonicality needs only the remainder operation,
not correctness of the inverse, rank, or previously stored quotient. -/
def dividend (remainder : U64) (word : U32) : U64 :=
 U64.ofNat (remainder.val * 4294967296 + word.val)
def remWord (n : U64) : U32 := U32.ofNat (n.val % 2147483647)
def quotient (n : U64) : U32 := U32.ofNat (n.val / 2147483647)

theorem rem_canonical (n : U64) : PV_OWNK_ScalarOps.Canon (remWord n) := by
 have h : n.val % 2147483647 < 2147483647 := Nat.mod_lt _ (by omega)
 change (n.val % 2147483647) % 4294967296 < 2147483647
 rw [Nat.mod_eq_of_lt (by omega)]
 exact h

/-- Reverse-index division pass; each stored remainder is canonical, for
arbitrary input rank and arbitrary incoming remainder. -/
def pass : List U32 → U64 → List U32 × U32
 | [],remainder => ([],remWord remainder)
 | w::ws,remainder =>
  let n := dividend remainder w
  let rest := pass ws (U64.ofNat (n.val % 2147483647))
  (quotient n::rest.1,rest.2)

theorem pass_canonical (rank : List U32) (remainder : U64) :
 PV_OWNK_ScalarOps.Canon (pass rank remainder).2 := by
 induction rank generalizing remainder with
 | nil => exact rem_canonical remainder
 | cons w ws ih => exact ih _

/-- First four of the eight base_p_digits passes in core r0_transcript.rs.
The input may be any reduced rank: reduction correctness is unnecessary
for the canonical-output invariant. -/
def sample (rank : List U32) : Q :=
 let a := pass rank 0#u64
 let b := pass a.1 0#u64
 let c := pass b.1 0#u64
 let d := pass c.1 0#u64
 ⟨⟨a.2,b.2⟩,⟨c.2,d.2⟩⟩

theorem sample_canonical (rank : List U32) : Canon (sample rank) :=
 ⟨⟨pass_canonical _ _,pass_canonical _ _⟩,pass_canonical _ _,pass_canonical _ _⟩
#print axioms rem_canonical
#print axioms pass_canonical
#print axioms sample_canonical
end R1Z.PV_OWNL_SampleCanon
