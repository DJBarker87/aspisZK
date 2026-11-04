import NFS_QueryValuesPacket
import NFP_QueryAdvance
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_QueryInvariant
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts

def core (base : Ops) : Ops := NFP_ObserverErasure.erase
 (NFP_DotInstall.cohort (NFS_NEV_TailModel.fields (NFS_QueryOps.base base)))
theorem form (base : Ops) : NFS_QueryOps.installed base=NBF_Accumulate.install (core base) := rfl

structure Domain (p : verifier.Prepared) (start finish : Nat)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop where
 width : a.weights.val.length=64
 weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights
 rhs : NBO_TailDomain.WideCanonical a.rhs
 power : NBF_PowerStep.Canonical a.power
 rho : NBF_PowerStep.Canonical p.rho
 progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b)
 offset : b.terms.val+start=a.next.val
 upper : a.next.val≤finish

theorem active (p : verifier.Prepared) (start finish : Nat)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (d : Domain p start finish a b) (limit : finish≤22) (inside : a.next.val<finish) :
 NFS_AccumDomain.Input p a b := by
 refine ⟨d.width,d.weights,by omega,?_,d.rhs,d.power,d.rho,d.progress⟩
 have offset := d.offset
 omega

theorem step (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (start finish : Nat)
 (a after : verifier.Accumulator) (b pending : verifier.BatchedWeights)
 (d : Domain p start finish a b) (limit : finish≤22) (inside : a.next.val<finish)
 (run : verifier.candidate.query_values (NFS_QueryOps.installed base)
  proof p a g none geometry b=ok (.Ok (after,pending))) :
 Domain p start finish after pending := by
 have input := active p start finish a b d limit inside
 have native : verifier.candidate.query_values (NBF_Accumulate.install (core base))
   proof p a g none geometry b=ok (.Ok (after,pending)) := by simpa only [←form] using run
 obtain ⟨weights,next,terms,progress⟩ := NFP_QueryAdvance.accepted (core base)
  proof p a after g geometry b pending d.width input.global input.localActive d.progress d.power native
 obtain ⟨query,opening,dots,inverse,circle,values,line,node,
  hquery,hopening,hdots,hinverse,hcircle,hline,haccum⟩ :=
  NBF_QueryCuts.accepted (NFS_QueryOps.installed base) proof p a after g none geometry b pending run
 have canonical := NFS_AccumDomain.line _ values inverse line hline
 have fields : NBO_TailDomain.NBC_Fields (core base) :=
  NBO_FieldSemantics.fields (core base) ⟨fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl⟩
 have tail := NBO_TailDomain.accumulate (core base) fields p a after node line b pending
  d.width d.progress d.power d.rho d.rhs canonical (by simpa only [←form] using haccum)
 refine ⟨?_,?_,tail.1,tail.2,d.rho,progress,?_,?_⟩
 · rw [weights];exact d.width
 · simpa only [NEV_AccumulateCarriers.fromAccumulator,weights] using d.weights
 · have offset := d.offset
   omega
 · omega
#print axioms form
#print axioms active
#print axioms step
end AspisR1.NFS_QueryInvariant
end
