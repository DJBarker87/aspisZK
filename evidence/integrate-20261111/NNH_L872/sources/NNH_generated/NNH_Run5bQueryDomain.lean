import NNH_Tx2OpenSlots
import NFS_QueryInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bQueryDomain
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem k (x : aspis_core.field.QM31) (h : NID_ResumeCanonical.KCanonical x) :
 NBF_PowerStep.Canonical x := by
 rcases h with ⟨a,b,c,d⟩
 intro i
 fin_cases i <;> assumption

theorem e (x : aspis_core.field.wide_exact.WideExact) (h : NID_ResumeCanonical.ECanonical x) :
 NBO_TailDomain.WideCanonical x := ⟨k x.c0 h.1,k x.c1 h.2⟩

theorem initial (r : NP6_StdModel.Reservation) (p : verifier.Prepared)
 (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (d : NID_ResumeFields.Domain p a) (next : a.next=10#usize)
 (run : NJJ_Common.pending r a.weights.deref = .ok (.Ok pending)) :
 NFS_QueryInvariant.Domain p 10 22 a pending := by
 have native := run
 change Port3_NativePendingInstall.source (NJC_FilledClause.reserved r) a.weights.deref = _ at native
 have fs := Port3_NativePendingInstall.accepted_fields _ _ pending d.width native
 have reference := native
 rw [Port3_NativePendingInstall.reference_eq _ a.weights.deref d.width] at reference
 have progress := Port3_PendingInstall.accepted_progress _ a.weights.deref pending d.width reference
 refine ⟨d.width,?_,e a.rhs d.rhs,k a.power d.power,k p.rho d.rho,?_,?_,?_⟩
 · intro raw member
   change raw ∈ (a.weights.val.map NEV_AccumulateCarriers.fromQ) at member
   obtain ⟨value,member,rfl⟩ := List.mem_map.mp member
   rw [NEV_AccumulateCarriers.q_reverse]
   exact k value (d.weights value member)
 · rw [fs.2.2.1]
   exact progress
 · rw [fs.2.2.1,next]
   rfl
 · rw [next]
   decide
#print axioms k
#print axioms e
#print axioms initial
end AspisR1.NNH_Run5bQueryDomain
end
