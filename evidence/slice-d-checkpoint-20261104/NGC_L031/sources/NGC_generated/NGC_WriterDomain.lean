import NGC_PreparationBoundary
import NGC_QueryPoststate
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_WriterDomain
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes3Namespaces OraclePortCkptAbi4Decode
/-- Checkpoint prestate derived from the SAME loop output and pending residues.
The only remaining preparation input is the named NFW field predicate. -/
theorem after_finish (p : verifier.Prepared) (a : verifier.Accumulator)
 (b : verifier.BatchedWeights) (d : NFS_QueryInvariant.Domain p 0 10 a b)
 (next : a.next.val=10) (prepared : NGC_PreparationBoundary.Fields p) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush b a.weights.deref=ok out ∧
 let after : verifier.Accumulator := {a with weights:=⟨out.val,out.property⟩}
 NGC_KNE_Caller.WriterDomain (toPrepared p) (toAccumulator after) ∧
 after.rhs=a.rhs ∧ after.power=a.power ∧ after.next=a.next := by
 obtain ⟨out,run,len,canonical,frame⟩ := NGC_FinishFrame.result_frame p 0 10 a b d
 let after : verifier.Accumulator := {a with weights:=⟨out.val,out.property⟩}
 have size : (toAccumulator after).weights.val.length=64 := by
  change (out.val.map toK).length=64
  simpa only [List.length_map] using len
 refine ⟨out,run,?_,rfl,rfl,rfl⟩
 refine ⟨prepared.variant,size,prepared.queries,?_,next⟩
 refine ⟨prepared.gamma,prepared.kappa,prepared.alpha,NGC_PreparationBoundary.canonicalK p.rho d.rho,
  prepared.semanticAlpha,prepared.coordinates,prepared.claim,
  NGC_PreparationBoundary.canonicalE a.rhs d.rhs,
  NGC_PreparationBoundary.canonicalK a.power d.power,?_⟩
 intro j
 change Canonical ((out.val.map toK)[j.val]'_)
 rw [List.getElem_map]
 exact canonical _ (List.getElem_mem _)
/-- The derived post-loop invariant is threaded directly into finish; neither
an accepted checkpoint nor an unrelated prepared/accumulator witness appears. -/
theorem from_query_loop (base : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
 (b pending : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p 0 10 a b)
 (start : a.next.val=0) (prepared : NGC_PreparationBoundary.Fields p)
 (accepted : Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 10#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let written : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 NGC_KNE_Caller.WriterDomain (toPrepared p) (toAccumulator written) ∧
 written.rhs=after.rhs ∧ written.power=after.power ∧ written.next=after.next := by
 have post := NGC_QueryPoststate.tx1 base proof p a after g geometry b pending domain start accepted
 exact after_finish p after pending post.1 post.2 prepared
#print axioms after_finish
#print axioms from_query_loop
end AspisR1.NGC_WriterDomain
end
