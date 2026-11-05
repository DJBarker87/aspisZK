import NGL_SnapshotModel
set_option autoImplicit false
namespace NHJ_StdCopy
open Aeneas Aeneas.Std Result
abbrev Bytes := Slice U8

theorem map_bytes (xs : List U8) :
    xs.mapM (fun x => Result.ok x) = Result.ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,ih]
    rfl

theorem list_clone (xs : List U8) :
    Aeneas.Std.List.clone (fun x => Result.ok x) xs = ok ⟨xs,rfl⟩ := by
  unfold Aeneas.Std.List.clone
  split
  · rename_i v returned
    have same : v = xs := Result.ok.inj (returned.symm.trans (map_bytes xs))
    subst v
    rfl
  · rename_i err returned
    have bad := (map_bytes xs).symm.trans returned
    cases bad
  · rename_i returned
    have bad := (map_bytes xs).symm.trans returned
    cases bad

theorem to_vec_exact (bytes : Bytes) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 bytes = ok bytes := by
  change Slice.clone (fun x => Result.ok x) bytes = ok bytes
  unfold Slice.clone
  rw [list_clone]
  rfl

def copy (bytes : Bytes) := alloc.slice.Slice.to_vec core.clone.CloneU8 bytes

theorem length_law : NGL_SnapshotModel.CopyLengthLaw copy := by
  intro bytes v returned
  unfold copy at returned
  rw [to_vec_exact] at returned
  have same := Result.ok.inj returned
  subst v
  rfl
#print axioms map_bytes
#print axioms list_clone
#print axioms to_vec_exact
#print axioms length_law
end NHJ_StdCopy
