import NDO_JFy_PreweightedCell
import NDO_FIw_PackTotal
import RPv_FIx_PreweightedGroup
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PreweightedGroup
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)

theorem source {N : Usize} (packed : Array field.QM31 24#usize) (group start : Usize) (a : Array field.QM31 N)
    (hp : canonical packed) (ha : canonical a) (hg : group.val<24) (bound : start.val+N.val≤96) :
    ∃ out,FIx_PreweightedGroup.run packed group start a=ok out ∧ canonical out := by
  obtain ⟨lanes,hl,hlc⟩ := JFy_PreweightedCell.gather a start group ha bound hg
  obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read packed group hg hp
  obtain ⟨p,pack,hpc⟩ := FIw_PackTotal.source (Array.to_slice lanes) lanes.property hlc
  obtain ⟨next,hn,hnc,_⟩ := FIv_PreparedTotal.add q p hqc hpc
  obtain ⟨out,ho,hoc⟩ := JFy_ArrayTotal.update packed group next hg hp hnc
  refine ⟨out,?_,hoc⟩
  unfold FIx_PreweightedGroup.run
  rw [hl,bind_tc_ok,hq,bind_tc_ok]
  simp only [lift,bind_tc_ok]
  rw [pack,bind_tc_ok,hn,bind_tc_ok,ho]
#print axioms source
end AspisR1.JFy_PreweightedGroup
end
