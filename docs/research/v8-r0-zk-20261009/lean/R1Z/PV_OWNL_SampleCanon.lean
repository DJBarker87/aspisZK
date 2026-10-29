import R1Z.PV_OWNL_SampleWord
set_option autoImplicit false
namespace R1Z.PV_OWNL_SampleCanon
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNL_SampleWord
/-- core r0_transcript.rs base_p_digits: high-word-first pass, retaining
quotient stores. Incoming remainder bound is an inductive invariant. -/
def pass : List U32 → U64 → List U32 × U32
 | [],remainder => ([],truncate remainder)
 | w::ws,remainder =>
  let n := dividend remainder w
  let rest := pass ws (rem64 n)
  (quotient n::rest.1,rest.2)

theorem pass_canonical (rank : List U32) (remainder : U64)
 (hr : remainder.val < 2147483647) :
 PV_OWNK_ScalarOps.Canon (pass rank remainder).2 := by
 induction rank generalizing remainder with
 | nil => exact truncate_canonical remainder hr
 | cons w ws ih => exact ih _ (rem_bound _)

/-- First four of the eight base_p_digits passes. The rank supplied by
reduce_rank may be arbitrary for the canonical-output invariant. -/
def sample (rank : List U32) : Q :=
 let a := pass rank 0#u64
 let b := pass a.1 0#u64
 let c := pass b.1 0#u64
 let d := pass c.1 0#u64
 ⟨⟨a.2,b.2⟩,⟨c.2,d.2⟩⟩

theorem sample_canonical (rank : List U32) : Canon (sample rank) :=
 ⟨⟨pass_canonical _ _ (by change 0 < 2147483647; omega),
    pass_canonical _ _ (by change 0 < 2147483647; omega)⟩,
    pass_canonical _ _ (by change 0 < 2147483647; omega),
    pass_canonical _ _ (by change 0 < 2147483647; omega)⟩
#print axioms pass_canonical
#print axioms sample_canonical
end R1Z.PV_OWNL_SampleCanon
