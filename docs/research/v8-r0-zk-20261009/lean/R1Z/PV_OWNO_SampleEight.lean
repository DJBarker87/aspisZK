import R1Z.PV_OWNL_SampleCanon
set_option autoImplicit false
namespace R1Z.PV_OWNO_SampleEight
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNL_SampleWord
attribute [local irreducible] u32 u64 dividend quotient rem64 truncate

/-- A division pass retains every quotient store, in high-word-first order.
The dividend operation may be the actual U64 shift/OR. Canonicality is
independent of its value and of the rank-reduction implementation. -/
structure State where
 words : List U32
 remainder : U64

def step (combine : U64 → U32 → U64) (s : State) (w : U32) : State :=
 let n := combine s.remainder w
 ⟨s.words ++ [quotient n],rem64 n⟩

theorem fold_bound (combine : U64 → U32 → U64) (rank : List U32) (s : State)
 (hr : s.remainder.val < 2147483647) :
 (rank.foldl (step combine) s).remainder.val < 2147483647 := by
 induction rank generalizing s with
 | nil => exact hr
 | cons w ws ih =>
  rw [List.foldl_cons]
  exact ih (step combine s w) (rem_bound _)

def pass (combine : U64 → U32 → U64) (rank : List U32) : List U32 × U32 :=
 let s := rank.foldl (step combine) ⟨[],0#u64⟩
 (s.words,truncate s.remainder)

theorem pass_canonical (combine : U64 → U32 → U64) (rank : List U32) :
 PV_OWNK_ScalarOps.Canon (pass combine rank).2 := by
 apply truncate_canonical
 exact fold_bound combine rank ⟨[],0#u64⟩ (by change 0 < 2147483647; omega)

/-- All eight array::from_fn calls execute, passing the stored quotient rank
from each call to the next. No mutable restoration is discarded. -/
def digits (combine : U64 → U32 → U64) : Nat → List U32 → List U32
 | 0,_ => []
 | n+1,rank => let p := pass combine rank; p.2 :: digits combine n p.1

theorem digits_length (combine : U64 → U32 → U64) (n : Nat) (rank : List U32) :
 (digits combine n rank).length = n := by
 induction n generalizing rank with
 | zero => rfl
 | succ n ih => simp only [digits,List.length_cons,ih]

theorem digits_canonical (combine : U64 → U32 → U64) (n : Nat) (rank : List U32) :
 ∀ x ∈ digits combine n rank, PV_OWNK_ScalarOps.Canon x := by
 induction n generalizing rank with
 | zero => intro x hx; cases hx
 | succ n ih =>
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact pass_canonical combine rank
  · exact ih _ x hx

/-- The returned QM31 uses the first four stored digits; later stores are
performed on the rank and on distinct output-array entries. -/
def sample (combine : U64 → U32 → U64) (rank : List U32) : Q :=
 let d := digits combine 8 rank
 ⟨⟨d[0]?.getD (0#u32),d[1]?.getD (0#u32)⟩,
  ⟨d[2]?.getD (0#u32),d[3]?.getD (0#u32)⟩⟩

theorem sample_canonical (combine : U64 → U32 → U64) (rank : List U32) :
 Canon (sample combine rank) := by
 have getCanon : ∀ i, PV_OWNK_ScalarOps.Canon
   ((digits combine 8 rank)[i]?.getD (0#u32)) := by
  intro i
  cases he : (digits combine 8 rank)[i]? with
  | none => change (0#u32).val < 2147483647; change 0 < 2147483647; omega
  | some x =>
   change PV_OWNK_ScalarOps.Canon x
   exact digits_canonical combine 8 rank x (List.mem_of_getElem? he)
 exact ⟨⟨getCanon 0,getCanon 1⟩,getCanon 2,getCanon 3⟩

#print axioms fold_bound
#print axioms pass_canonical
#print axioms digits_length
#print axioms digits_canonical
#print axioms sample_canonical
end R1Z.PV_OWNO_SampleEight
