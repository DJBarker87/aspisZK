import R1Z.PV_RunJoin_LiftRow63
import R1Z.PV_RunJoin_Vector44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftPayload63
open Aeneas Aeneas.Std Result
open PV_RunJoin_LiftRow63

def entry (column : alloc.vec.Vec aspis_core.field.M31) (row : Nat) : aspis_core.field.M31 :=
  column.val[row]?.getD 0#u32

def payload (column : alloc.vec.Vec aspis_core.field.M31) (row : Nat) : Nat → List Q
  | 0 => []
  | n+1 => PV_RunJoin_LiftCell63.lifted (entry column row)::payload column (row+1) n

theorem length (column : alloc.vec.Vec aspis_core.field.M31) (row n : Nat) :
    (payload column row n).length=n := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih => simp only [payload,List.length_cons,ih]

theorem read (column : alloc.vec.Vec aspis_core.field.M31) (row : Usize)
    (bound : row.val<column.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) column row=
      ok (entry column row.val) := by
  obtain ⟨m,hm,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec column row bound)
  rw [alloc.vec.Vec.index_slice_index,hm]
  simp only [entry,List.getElem?_eq_getElem bound,Option.getD_some]
  exact congrArg Result.ok he

#print axioms entry
#print axioms payload
#print axioms length
#print axioms read
end R1Z.PV_RunJoin_LiftPayload63
