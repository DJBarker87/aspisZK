import NFS_CallerDomains
import NFS_LoopTrace
import NFP_GeometryDomains
import NFP_NodeDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_PacketRoot
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts NFP_TraceTypes NFG_QueryLoopDefs

/-- Input data only. Prepared/powers/prepare producers remain external. -/
structure Domain (proof : Slice U8) (p : verifier.Prepared) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (start : Nat) (finish : Usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop where
 proofLength : proof.val.length=57607
 finishCase : finish=10#usize ∨ finish=22#usize
 limit : finish.val≤22
 invariant : NFS_QueryInvariant.Domain p start finish.val a b
 gCanonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)
 alpha0 : Port4C_QueryArithmetic.CanonE (p.alpha.val[0]'(by rw [p.alpha.property];decide))
 alpha1 : Port4C_QueryArithmetic.CanonE (p.alpha.val[1]'(by rw [p.alpha.property];decide))
 geometryStart : geometry.start.val=start
 inverseLength : geometry.inverses.val.length=finish.val-geometry.start.val
 lineLength : geometry.line_z.val.length=finish.val-geometry.start.val
 inverseCanonical : ∀ row∈geometry.inverses.val,∀ x∈row.val,x.val<2147483647
 lineCanonical : ∀ x∈geometry.line_z.val,x.val<2147483647

theorem geometry (proof : Slice U8) (p : verifier.Prepared) (g : Array E 29#usize)
 (geo : verifier.QueryGeometry) (start : Nat) (finish : Usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (domain : Domain proof p g geo start finish a b) (active : a.next.val<finish.val) :
 ∃ inverse z,Port5Q1_GeometryBinding.forQuery geo a.next=ok inverse ∧
 alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
  geo.line_z (Usize.wrapping_sub a.next geo.start)=ok z ∧
 (∀ x∈inverse.val,x.val<2147483647) ∧ z.val<2147483647 := by
 have offset := domain.invariant.offset
 exact NFP_GeometryDomains.reads geo a.next finish (by rw [domain.geometryStart];omega)
  active domain.inverseLength domain.lineLength domain.inverseCanonical domain.lineCanonical

/-- The actual node dictionary is scalar M31 throughout. Conservative typed
CM31/QM31/WideExact receiver alternatives have no call in this body. -/
theorem node (seed : Ops) (z : U32) :
 (do let square ← (NFS_CallerDomains.ops seed).op7 z z
     let doubled ← (NFS_CallerDomains.ops seed).op8 square
     let one ← (NFS_CallerDomains.ops seed).op5
     (NFS_CallerDomains.ops seed).op6 doubled one) = NFP_NodeDictionary.probeNode z := rfl

theorem query (seed : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geo : verifier.QueryGeometry) (start : Nat) (finish : Usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) (qPlace gPlace : Nat)
 (domain : Domain proof p g geo start finish a b) (active : a.next.val<finish.val) :
 NFS_QueryValuesPacket.run (NFS_CallerDomains.select seed) proof p a g geo b qPlace gPlace =
 NFP_QueryTrace.run (NFS_CallerDomains.ops seed) proof p a g geo b :=
 NFS_QueryValuesPacket.source _ _ _ _ _ _ _ _ _ domain.gCanonical
  (NFS_QueryInvariant.active p start finish.val a b domain.invariant domain.limit active)

theorem loop (seed : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geo : verifier.QueryGeometry) (start : Nat) (finish : Usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) (qPlace gPlace fuel : Nat)
 (domain : Domain proof p g geo start finish a b) :
 NFS_LoopTraceDefs.run
  (fun a b=>NFS_QueryValuesPacket.run (NFS_CallerDomains.select seed) proof p a g geo b qPlace gPlace)
  finish fuel (.Ok (a,b)) =
 NFS_LoopTraceDefs.run
  (fun a b=>NFP_QueryTrace.run (NFS_CallerDomains.ops seed) proof p a g geo b)
  finish fuel (.Ok (a,b)) :=
 NFS_LoopTrace.source _ _ _ _ _ _ _ start finish domain.limit domain.gCanonical fuel (.Ok (a,b)) domain.invariant
#print axioms geometry
#print axioms node
#print axioms query
#print axioms loop
end AspisR1.NFS_PacketRoot
end
