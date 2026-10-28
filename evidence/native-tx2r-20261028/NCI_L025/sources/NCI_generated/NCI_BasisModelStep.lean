import Port3_NativeQueryBody
set_option autoImplicit false
namespace AspisR1.NCI_BasisModelStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeQueryBody

theorem source_step (ops : Ops) (node old product : aspis_core.field.M31)
    (n j target : Usize) (iter nextIter : core.ops.range.Range Usize)
    (basis after : Array aspis_core.field.M31 256#usize)
    (Next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some j,nextIter))
    (Read : Array.index_usize basis j=ok old)
    (Mul : ops.op7 old node=ok product)
    (Index : lift (Usize.wrapping_add n j)=ok target)
    (Write : Array.update basis target product=ok after) :
    verifier.accumulate_batched_with_node_loop0_loop0.body ops node n iter basis=
      ok (cont (nextIter,after)) := by
  simp only [verifier.accumulate_batched_with_node_loop0_loop0.body,Next,bind_tc_ok]
  change (do
    let m ← Array.index_usize basis j
    let value ← ops.op7 m node
    let index ← lift (Usize.wrapping_add n j)
    let result ← Array.update basis index value
    ok (cont (nextIter,result))) = _
  rw [Read,bind_tc_ok,Mul,bind_tc_ok,Index,bind_tc_ok,Write,bind_tc_ok]

theorem index_value (n j : Usize) (hn : n.val≤32) (hj : j.val<n.val) :
    (Usize.wrapping_add n j).val=n.val+j.val := by
  scalar_tac

theorem read_exists (basis : Array aspis_core.field.M31 256#usize) (j : Usize)
    (hj : j.val<256) : ∃ old, Array.index_usize basis j=ok old := by
  obtain ⟨old,run,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec basis j (by simpa only [basis.property] using hj))
  exact ⟨old,run⟩

#print axioms index_value
#print axioms read_exists
#print axioms source_step
end AspisR1.NCI_BasisModelStep
