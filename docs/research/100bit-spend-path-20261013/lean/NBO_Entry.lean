import NBO_Composite
set_option autoImplicit false
noncomputable section
namespace NBO_Entry
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Exact pre-query cuts. There is no query/flush result or accepted final
output in this predicate, so it also describes entries that later reject. -/
def Prelude (base : VTop_Stages.Ops) (reserved : Bool)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) (geometry : verifier.QueryGeometry) : Prop :=
 ∃ zero preparation root parsed,
 split.val=10 ∧ base.op3 proof=ok (.Ok parsed) ∧ base.op4 proof=ok (.Ok ()) ∧
 base.op1=ok zero ∧
 base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (preparation,g) ∧
 core.result.Result.Insts.CoreOpsTry.branch preparation=ok (.Continue p) ∧
 (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a) ∧
 base.op5 D proof p root 0#usize hash=ok (.Ok ()) ∧
 base.op11 p.queries 0#usize split=ok (.Ok geometry) ∧
 Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b)
def QueryBound (queries : Array U32 22#usize) : Prop :=
 ∀ i : Usize, i.val<10 → ∀ q, Array.index_usize queries i=ok q → q.val<262144
/-- The exact remaining parser/geometry numeric projections needed by the
native harness domains. These are lower source-unit statements, not trust. -/
structure NBC_Bounds (base : VTop_Stages.Ops) : Prop where
 parse : ∀ proof parsed, base.op3 proof=ok (.Ok parsed) → proof.val.length=57607
 queries : ∀ queries split geometry,
   split.val=10 → base.op11 queries 0#usize split=ok (.Ok geometry) → QueryBound queries
/-- All producer/constructor facts come from the SAME pre-query cuts. -/
theorem domains (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (producers : NBO_ProducerDomains.NBA_NBC base ops) (bounds : NBC_Bounds base)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) (geometry : verifier.QueryGeometry)
 (entry : Prelude base reserved D hash semantic proof split p g a b geometry) :
 proof.val.length=57607 ∧ NBO_ProducerDomains.Prepared p g ∧
 NBO_QueryDomains.GeometryDomain geometry ∧ QueryBound p.queries ∧
 (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a) ∧
 Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b) ∧
 (∀ (i : Usize) q, i.val<10 → ops.op11 proof i=ok q → NBO_CircleDomain.OpeningDomain q) := by
 obtain ⟨zero,preparation,root,parsed,split10,parse,scan,hzero,prep,branch,initial,batch,geo,pending⟩:=entry
 exact ⟨bounds.parse proof parsed parse,
   producers.prepare D hash semantic proof (Array.repeat 29#usize zero) preparation g p prep branch,
   producers.geometry p.queries split geometry split10 geo,bounds.queries p.queries split geometry split10 geo,
   initial,pending,fun i q active read=>producers.scanOpening proof i q scan active read⟩
/-- Complete composite Result equality from the SAME entry, with no query
success or independently chosen preparation/geometry/domain witness. -/
theorem association (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (producers : NBO_ProducerDomains.NBA_NBC base ops) (bounds : NBC_Bounds base)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights) (geometry : verifier.QueryGeometry)
 (entry : Prelude base reserved D hash semantic proof split p g a b geometry) :
 NBO_Composite.source ops proof p a g geometry b=NBO_Composite.reference ops proof p a g geometry b := by
 obtain ⟨length,prepared,domain,queryBound,initial,pending,opening⟩ :=
   domains base reserved ops producers bounds D hash semantic proof split p g a b geometry entry
 exact NBO_Composite.association base reserved ops lower bindings proof p prepared.tail g geometry
   domain a b initial pending
#print axioms domains
#print axioms association
end NBO_Entry
end
