import NBO_Entry
set_option autoImplicit false
noncomputable section
namespace NBO_EveryCaller
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- All numeric/field/row domains at EVERY reached query entry, including
one which subsequently rejects, fails or diverges. Source producer laws remain
exact named lower obligations; no successful query return is a hypothesis. -/
theorem ready (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (producers : NBO_ProducerDomains.NBA_NBC base ops) (bounds : NBO_Entry.NBC_Bounds base)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (initial a : verifier.Accumulator) (pending b : verifier.BatchedWeights)
 (geometry : verifier.QueryGeometry)
 (entry : NBO_Entry.Prelude base reserved D hash semantic proof split p g initial pending geometry)
 (prefixRun : NBO_AllCalls.Prefix ops proof p g geometry initial pending a b)
 (active : a.next.val<10) :
 proof.val.length=57607 ∧ NBO_QueryRhs.Good a b ∧
 a.weights=initial.weights ∧ NBO_AllCalls.CanonicalWeights a.weights ∧
 NBO_ProducerDomains.Prepared p g ∧
 (∃ q, Array.index_usize p.queries a.next=ok q ∧ q.val<262144) ∧
 (∃ z, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
   geometry.line_z (Usize.wrapping_sub a.next geometry.start)=ok z ∧ z.val<2147483647) ∧
 (∀ q, ops.op11 proof a.next=ok q → NBO_CircleDomain.OpeningDomain q) := by
 obtain ⟨length,prepared,domain,queryBound,initRun,pendingRun,opening⟩ :=
   NBO_Entry.domains base reserved ops producers bounds D hash semantic proof split p g
     initial pending geometry entry
 obtain ⟨good,weights,canonical,nextBound⟩ := NBO_AllCalls.reached base reserved ops lower bindings
   proof p prepared.tail g geometry domain initial a pending b initRun pendingRun prefixRun
 have querySize : a.next.val<p.queries.val.length := by rw [p.queries.property];change a.next.val<22;omega
 obtain ⟨q,hq,hqval⟩ := WP.spec_imp_exists (Array.index_usize_spec p.queries a.next querySize)
 obtain ⟨order,offset,z,hz,hcanonical⟩ := NBO_GeometryDomain.node_input geometry domain a.next active
 exact ⟨length,good,weights,canonical,prepared,⟨q,hq,queryBound a.next active q hq⟩,
   ⟨z,hz,hcanonical⟩,fun q read=>opening a.next q active read⟩
#print axioms ready
end NBO_EveryCaller
end
