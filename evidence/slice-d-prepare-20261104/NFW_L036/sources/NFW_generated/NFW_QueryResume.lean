import NFW_QueryStart
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_QueryResume
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

def toRowQ (x : aspis_core.field.QM31) : S8OwnedP6ValueModel.Q :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def rowWeights (a : verifier.Accumulator) : S8OwnedP6Finish.Weights :=
 ⟨a.weights.val.map toRowQ,by simpa using a.weights.property⟩
def pending (a : verifier.Accumulator) : verifier.BatchedWeights :=
 ⟨S7Kani3CallerTrace.initialRaw (rowWeights a),0#usize⟩

theorem progress (a : verifier.Accumulator) (width : a.weights.val.length=64) :
 S7JoinRowsTrace.Progress 0 0 (Port3_RowsInstall.toBW (pending a)) := by
 exact S7JoinQueryRows.initial_progress (rowWeights a) (by simp [rowWeights,width])
/-- Reset pending is constructed from the SAME resumed weights. No old pending
state or unproved whole query-loop domain is supplied. Resume's primitive
carrier bounds remain producer obligations at the slice boundary. -/
theorem domain (p : verifier.Prepared) (a : verifier.Accumulator)
 (width : a.weights.val.length=64)
 (weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights)
 (rhs : NBO_TailDomain.WideCanonical a.rhs) (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho) (start : a.next.val=10) :
 NFS_QueryInvariant.Domain p 10 22 a (pending a) := by
 refine ⟨width,weights,rhs,power,rho,progress a width,?_,?_⟩
 · change 0+10=a.next.val
   omega
 · omega

theorem tx2 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (width : a.weights.val.length=64)
 (weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights)
 (rhs : NBO_TailDomain.WideCanonical a.rhs) (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho) (start : a.next.val=10)
 (gamma : NFN_LPi_FieldValues.NE) (canonicalGamma : NFN_LPi_FieldValues.canonE gamma)
 (g : Array NFN_LPi_FieldValues.NE 29#usize)
 (powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat) :
 NFG_QueryLoopDefs.run
  (NFS_QueryLoopRoot.child base proof p (FIp_DotsAdapter.fromArray g) geometry qPlace gPlace)
  22#usize 12 (.Ok (a,pending a)) =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof p a
  (FIp_DotsAdapter.fromArray g) none geometry (pending a) 22#usize := by
 exact NFS_QueryLoopRoot.tx2 base proof p a (FIp_DotsAdapter.fromArray g) geometry
  (pending a) qPlace gPlace (NFW_PowersDomain.query_domain gamma canonicalGamma g powers)
  (domain p a width weights rhs power rho start) start
#print axioms progress
#print axioms domain
#print axioms tx2
end AspisR1.NFW_QueryResume
