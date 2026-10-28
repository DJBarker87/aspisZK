import NDO_JFy_PublicCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_FrontierCanonical
open Aeneas Aeneas.Std Result FIq_Native
open JFy_PublicCanonical (p P digest)

theorem before : ∀ row∈p.transition.live_snapshot.frontier.val,∀ x∈row.val,x.val<P := by
  change ∀ row∈JFt_SnapshotValue.value.frontier.val,∀ x∈row.val,x.val<P
  intro row hr
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hr
  subst row
  have ib : i<20 := by simpa only [JFt_SnapshotValue.value.frontier.property,show (20#usize).val=20 from rfl] using hi
  exact digest _ (JFu_DigestSliceCanonical.source _ _ (JFt_SnapshotValue.frontier ⟨i,ib⟩))
#print axioms before

theorem root : ∀ x∈p.transition.candidate_afterstate.next_root.val,x.val<P := digest _ JFt_Digest22.canonical
#print axioms root

theorem after : ∀ row∈p.transition.candidate_afterstate.next_frontier.val,∀ x∈row.val,x.val<P := by
  change ∀ row∈JFt_AfterstateValue.value.next_frontier.val,∀ x∈row.val,x.val<P
  intro row hr
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hr
  subst row
  have ib : i<20 := by simpa only [JFt_AfterstateValue.value.next_frontier.property,show (20#usize).val=20 from rfl] using hi
  exact digest _ (JFt_AfterstateValue.frontier ⟨i,ib⟩)
#print axioms after
end AspisR1.JFy_FrontierCanonical
end
