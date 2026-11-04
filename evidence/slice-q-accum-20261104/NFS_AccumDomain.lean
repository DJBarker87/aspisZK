import NFS_NEV_AccumPacket
import SAQ_LineQuery
import NFP_DotDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_AccumDomain
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open NEV_AccumulateCarriers

/-- Caller data only. Prepared/powers producers remain out of slice. -/
structure Input (p : verifier.Prepared) (a : verifier.Accumulator)
 (b : verifier.BatchedWeights) : Prop where
 width : a.weights.val.length=64
 weightsCanonical : NFS_NEV_WeightDomains.Canonical (fromAccumulator a).weights
 global : a.next.val<22
 localActive : b.terms.val<22
 rhs : NBO_TailDomain.WideCanonical a.rhs
 power : NBF_PowerStep.Canonical a.power
 rho : NBF_PowerStep.Canonical p.rho
 progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b)

/-- The actual line child establishes the value domain passed to accumulation.
No independently successful line call or accumulation result is supplied. -/
theorem line (alpha : E) (values : Dots) (inverse : Array U32 5#usize) (out : E)
 (run : SAQ_LineQuery.line alpha values inverse=ok out) :
 NBO_TailDomain.WideCanonical out := (SAQ_LineQuery.exact_line alpha values inverse out run).2

theorem domain (p : verifier.Prepared) (a : verifier.Accumulator)
 (b : verifier.BatchedWeights) (value : E) (input : Input p a b)
 (canonical : NBO_TailDomain.WideCanonical value) :
 NFS_NEV_AccumPacket.Domain (fromPrepared p) (fromAccumulator a) (fromE value) (fromWeights b) := by
 constructor
 · simpa only [fromAccumulator,mapVec,List.length_map] using input.width
 · exact input.weightsCanonical
 · exact input.global
 · exact input.localActive
 · simpa only [e_reverse] using canonical
 · simpa only [fromAccumulator,e_reverse] using input.rhs
 · simpa only [fromAccumulator,q_reverse] using input.power
 · simpa only [fromPrepared,q_reverse] using input.rho
 · simpa only [fromWeights,weights_reverse] using input.progress
#print axioms line
#print axioms domain
end AspisR1.NFS_AccumDomain
end
