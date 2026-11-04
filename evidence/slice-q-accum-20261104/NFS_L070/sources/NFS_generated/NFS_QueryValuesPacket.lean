import NFS_DotTrace
import NFS_TraceBack
import NFS_FoldInstall
import NFP_QueryTrace
import NFP_RejectionTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_QueryValuesPacket
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes Port3_NativeQueryBody

def run (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (qPlace gPlace : Nat) : M Out := do
 let ops := NFS_QueryOps.installed base
 let (u,q,dots) ← NFP_TraceHead.run (NFP_DotInstall.oracle ops qPlace gPlace) proof p a g
 let (inverse,_,values,bad) ← NFP_TraceFront.run ops p a geometry u q dots
 if bad then pure (.Err verifier.Error.Query)
 else NFS_TraceBack.run base p a geometry pending inverse values

/-- Complete ordered caller trace after substituting the CLOSED dot and
accumulation children on their SAME inputs. Other callback slots are explicit. -/
theorem source (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (input : NFS_AccumDomain.Input p a pending) :
 run base proof p a g geometry pending qPlace gPlace =
 NFP_QueryTrace.run (NFS_QueryOps.installed base) proof p a g geometry pending := by
 unfold run NFP_QueryTrace.run
 rw [NFS_DotTrace.head _ _ _ _ _ _ _ canonical]
 simp only [NFS_TraceBack.installed base p a geometry pending _ _ input]
 rfl

theorem result (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (input : NFS_AccumDomain.Input p a pending) :
 (run base proof p a g geometry pending qPlace gPlace).result =
 verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geometry pending := by
 rw [source _ _ _ _ _ _ _ _ _ canonical input,NFP_QueryTrace.erased]
 rfl
#print axioms source
#print axioms result
end AspisR1.NFS_QueryValuesPacket
end
