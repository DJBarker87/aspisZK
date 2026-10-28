import R1Z.PV_RunJoin_PointArray34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeArray35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34
abbrev array (p : Nat → Q) := ProverCommitArray49.array 28#usize p

theorem read (p : Nat → Q) (i : Usize) (hi : i.val<28) :
    Array.index_usize (array p) i = .ok (p i.val) :=
  ProverCommitArray49.index _ _ i hi

theorem write (p : Nat → Q) (i : Usize) (hi : i.val<28) (q : Q) :
    Array.update (array p) i q = .ok (array (Function.update p i.val q)) :=
  ProverCommitArray49.update 28#usize p i hi q

/-- Array-to-slice reads retain exactly the same index failure boundary. -/
theorem slice_read {A : Type} {n : Usize} (a : Array A n) (i : Usize) :
    Slice.index_usize (Array.to_slice a) i = Array.index_usize a i := rfl

theorem slice_values {A : Type} (n : Usize) (f : Nat → A) (i : Usize) (hi : i.val<n.val) :
    Slice.index_usize (Array.to_slice (ProverCommitArray49.array n f)) i = .ok (f i.val) := by
  rw [slice_read,ProverCommitArray49.index n f i hi]

#print axioms read
#print axioms write
#print axioms slice_read
#print axioms slice_values
end R1Z.PV_RunJoin_MergeArray35
