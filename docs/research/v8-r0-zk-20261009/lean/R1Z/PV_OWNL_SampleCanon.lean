import R1Z.PV_OWNL_SampleWord
set_option autoImplicit false
namespace R1Z.PV_OWNL_SampleCanon
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNL_SampleWord
attribute [local irreducible] dividend rem64 quotient truncate u32 u64
structure State where
 words : List U32
 remainder : U64

def step (s : State) (w : U32) : State :=
 let n := dividend s.remainder w
 ⟨s.words ++ [quotient n],rem64 n⟩

theorem step_bound (s : State) (w : U32) :
 (step s w).remainder.val < 2147483647 := rem_bound _

theorem fold_bound (rank : List U32) (s : State)
 (hr : s.remainder.val < 2147483647) :
 (rank.foldl step s).remainder.val < 2147483647 := by
 induction rank generalizing s with
 | nil => exact hr
 | cons w ws ih =>
  rw [List.foldl_cons]
  exact ih (step s w) (step_bound s w)

/-- High-word-first source division pass. All quotient stores are retained. -/
def pass (rank : List U32) : List U32 × U32 :=
 let result := rank.foldl step ⟨[],0#u64⟩
 (result.words,truncate result.remainder)

theorem pass_canonical (rank : List U32) :
 PV_OWNK_ScalarOps.Canon (pass rank).2 := by
 apply truncate_canonical
 exact fold_bound rank ⟨[],0#u64⟩ (by change 0 < 2147483647; omega)

/-- First four of eight core base_p_digits passes. Subsequent passes cannot
modify these four stored output digits. Rank reduction may be arbitrary. -/
def sample (rank : List U32) : Q :=
 let a := pass rank
 let b := pass a.1
 let c := pass b.1
 let d := pass c.1
 ⟨⟨a.2,b.2⟩,⟨c.2,d.2⟩⟩

theorem sample_canonical (rank : List U32) : Canon (sample rank) :=
 ⟨⟨pass_canonical _,pass_canonical _⟩,pass_canonical _,pass_canonical _⟩
#print axioms step_bound
#print axioms fold_bound
#print axioms pass_canonical
#print axioms sample_canonical
end R1Z.PV_OWNL_SampleCanon
