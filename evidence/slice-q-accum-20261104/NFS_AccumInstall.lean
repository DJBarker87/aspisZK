import NFS_AccumDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_AccumInstall
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody NEV_AccumulateCarriers NFP_QueryCuts

def run (p : verifier.Prepared) (a : verifier.Accumulator) (node : U32)
 (value : E) (b : verifier.BatchedWeights) : Result (verifier.Accumulator × verifier.BatchedWeights) := do
 let out ← NEV_AccumulateRaw.accumulate_batched_with_node
  (fromPrepared p) (fromAccumulator a) node (fromE value) (fromWeights b)
 ok (NFS_NEV_TailModel.toPair out)

/-- SAME complete input records; the raw packet's domain is derived from
root inputs and the actual line return. No inner success is a premise. -/
theorem installed (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : E) (b : verifier.BatchedWeights)
 (input : NFS_AccumDomain.Input p a b) (canonical : NBO_TailDomain.WideCanonical value) :
 run p a node value b = verifier.accumulate_batched_with_node
  (NBO_AccumulateAssociation.sourceOps (NFS_NEV_TailModel.fields base)) p a node value b := by
 have d := NFS_AccumDomain.domain p a b value input canonical
 have h := NFS_NEV_AccumulateComplete.native base
  (fromPrepared p) (fromAccumulator a) node (fromE value) (fromWeights b)
  d.width (NFS_NEV_AccumPacket.raw_length _ _ _ _ d) d.global d.localActive
  d.valueCanonical d.rhsCanonical d.powerCanonical d.rhoCanonical
 simpa only [run,prepared_reverse,accumulator_reverse,e_reverse,weights_reverse] using h
#print axioms installed
end AspisR1.NFS_AccumInstall
end
