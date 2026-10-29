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

theorem complete (columns : Columns) (lane : Usize) (column : alloc.vec.Vec aspis_core.field.M31)
    (source : Array.index_usize columns lane=ok column) (n : Nat) (row : Usize)
    (bound : row.val+n≤column.length) (counter : row.val+n≤1024)
    (out : alloc.vec.Vec Q) (room : out.length+n≤Usize.max) :
    ∃ next, phase columns lane n out row=ok next ∧
      next.val=out.val ++ payload column row.val n := by
  induction n generalizing row out with
  | zero => exact ⟨out,rfl,by simp only [payload,List.append_nil]⟩
  | succ n ih =>
    have hr : row.val<column.length := by omega
    have more : row<1024#usize := by change row.val<1024;omega
    have inc := ProverCommitPairCounter47.next_val row more
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_Vector44.push out
      (PV_RunJoin_LiftCell63.lifted (entry column row.val)) (by omega)
    have ml : mid.length=out.length+1 := by
      change mid.val.length=out.val.length+1
      rw [hv,List.length_append,List.length_singleton]
    obtain ⟨next,hn,hnext⟩ := ih (Usize.wrapping_add row 1#usize)
      (by rw [inc];omega) (by rw [inc];omega) mid (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · simp only [phase,step,source,bind_tc_ok,read column row hr,hm]
      exact hn
    · rw [hnext,hv,inc,payload,List.append_assoc]
      rfl

#print axioms entry
#print axioms payload
#print axioms length
#print axioms read
#print axioms complete
end R1Z.PV_RunJoin_LiftPayload63
