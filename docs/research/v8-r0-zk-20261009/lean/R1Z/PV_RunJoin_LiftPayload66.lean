import R1Z.PV_RunJoin_LiftLiteral66
import R1Z.PV_RunJoin_LiftRow63
import R1Z.PV_RunJoin_BackendMRows58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftPayload66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column element)
abbrev Q := aspis_core.field.QM31

def payload (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane start n : Nat) : List Q :=
  List.ofFn (fun i : Fin n => PV_RunJoin_LiftCell63.lifted (element columns hlen lane (start+i.val)))

theorem read (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane row : Usize) (hl : lane.val<26) (hr : row.val<1024) :
    (do
      let col ← Array.index_usize columns lane
      let m ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) col row
      @host_semantic.lift (types base) (selected base heap box ops) m)=
      ok (PV_RunJoin_LiftCell63.lifted (element columns hlen lane.val row.val)) := by
  have hc : Array.index_usize columns lane=ok (column columns lane.val) := by
    rw [ProverCommitArrayIndex25.array_index_usize_ok columns lane hl]
    simp only [column,Nat.mod_eq_of_lt hl]
  rw [hc]
  simp only [bind_tc_ok]
  have hi : row.val<(column columns lane.val).val.length := by
    change row.val<(column columns lane.val).length
    rw [hlen _ hl]
    exact hr
  obtain ⟨m,hm,he⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec (column columns lane.val) row hi)
  rw [alloc.vec.Vec.index_slice_index,hm]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LiftLiteral66.complete base heap box ops]
  simp only [element,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr]
  rw [he]

theorem phase (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane : Usize) (hl : lane.val<26) (n : Nat) (row : Usize)
    (bound : row.val+n≤1024) (out : alloc.vec.Vec Q)
    (room : out.length+n≤Usize.max) :
    ∃ next,
      PV_RunJoin_LiftRow63.phase (@host_semantic.lift (types base) (selected base heap box ops))
        columns lane n out row=ok next ∧
      next.val=out.val++payload columns hlen lane.val row.val n := by
  induction n generalizing row out with
  | zero => exact ⟨out,rfl,by simp only [payload,List.ofFn_zero,List.append_nil]⟩
  | succ n ih =>
    have hr : row.val<1024 := by omega
    have ri : (Usize.wrapping_add row 1#usize).val=row.val+1 :=
      ProverCommitPairCounter47.next_val row hr
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_Vector44.push out
      (PV_RunJoin_LiftCell63.lifted (element columns hlen lane.val row.val)) (by omega)
    have ml : mid.length=out.length+1 := by
      change mid.val.length=out.val.length+1
      rw [hv,List.length_append,List.length_singleton]
    obtain ⟨next,hn,hnext⟩ := ih (Usize.wrapping_add row 1#usize)
      (by rw [ri];omega) mid (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · simp only [PV_RunJoin_LiftRow63.phase,PV_RunJoin_LiftRow63.step,bind_assoc_eq]
      rw [read base heap box ops columns hlen lane row hl hr]
      simp only [bind_tc_ok,hm,hn]
    · rw [hnext,hv,ri,List.append_assoc]
      apply congrArg (fun xs => out.val++xs)
      simp only [payload,List.ofFn_succ,List.singleton_append,Fin.val_zero,Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ]
      congr 2 <;> omega

#print axioms read
#print axioms phase
end R1Z.PV_RunJoin_LiftPayload66
