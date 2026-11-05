import NHW_Accumulate
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_QueryStep
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open NFP_QueryCuts NFP_TraceTypes NHW_QueryDictionary

theorem back (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) (input : NFS_AccumDomain.Input p a pending) :
 NFP_TraceBack.run (model base) p a geometry pending inverse values=
 NFP_TraceBack.run (NFS_QueryOps.installed (model base)) p a geometry pending inverse values := by
 rw [←NFS_TraceBack.source,←NFS_TraceBack.source]
 have same := NFS_TraceBack.model_congr (NFP_ObserverErasure.erase (model base))
   (fun node value=>verifier.accumulate_batched_with_node (NFP_ObserverErasure.erase (model base)) p a node value pending)
   (fun node value=>verifier.accumulate_batched_with_node (NFS_QueryOps.installed (model base)) p a node value pending)
   p a geometry pending inverse values (by
     intro alpha folded line node
     have canonical := NFS_AccumDomain.line alpha values inverse folded line
     exact NHW_Accumulate.source base p a node folded pending canonical input.rhs input.power input.rho)
 exact same

theorem head_same (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) :
 NFP_TraceHead.run (model base) proof p a g=
 NFP_TraceHead.run (NFS_QueryOps.installed (model base)) proof p a g := rfl

theorem front_same (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots) :
 NFP_TraceFront.run (model base) p a geometry u q dots=
 NFP_TraceFront.run (NFS_QueryOps.installed (model base)) p a geometry u q dots := rfl

theorem trace (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (input : NFS_AccumDomain.Input p a pending) :
 NFP_QueryTrace.run (model base) proof p a g geometry pending=
 NFP_QueryTrace.run (NFS_QueryOps.installed (model base)) proof p a g geometry pending := by
 simp only [NFP_QueryTrace.run,←head_same,←front_same,←back base p a geometry pending _ _ input]

theorem phase_erased (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) :
 verifier.candidate.query_values (NFP_ObserverErasure.erase (model base)) proof p a g none geometry pending=
 verifier.candidate.query_values (model base) proof p a g none geometry pending := by
 rw [NFP_QueryCuts.source,NFP_QueryCuts.source]
 rfl

theorem source (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (input : NFS_AccumDomain.Input p a pending) :
 verifier.candidate.query_values (model base) proof p a g none geometry pending=
 verifier.candidate.query_values (NFS_QueryOps.installed (model base)) proof p a g none geometry pending := by
 rw [←phase_erased,←NFP_QueryTrace.erased,trace base proof p a g geometry pending input,NFP_QueryTrace.erased]
 rfl
#print axioms back
#print axioms head_same
#print axioms front_same
#print axioms trace
#print axioms phase_erased
#print axioms source
end AspisR1.NHW_QueryStep
