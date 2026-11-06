import NKR_SumCopyAlgebraCombined
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopySplitCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NKR_SumCopyCollect (State Lookups)
open FIq_Native.pool_v1.pair_forest_copy_terminal

/--217 callsite projection,independent of103cell scratch. Reply is the raw
scalar returned unchanged by the native args window. Its field law remains
the existing CLOSED217 theorem,not this native projection. -/
def WeightCut (index : Fin 136) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (weight reply : U32) (passedLink : CompiledPoolV1PairForestLink)
 (passedAppend : U64) (passedVariant : PoolV1PairForestCompiledVariantV1) : Prop :=
 passedLink=NJL_EndpointLookup.link index ∧ passedAppend=append ∧ passedVariant=variant ∧ reply=weight

/--Endpoint-only native split:producer then consumer receive SAME returned
weight and full actual input payloads. Full103pointwise frames aggregate
only the arbitrary-cell assertion. Native log starts at1,ends3;this encodes
exactly TWO214 calls,not an unobserved217 call. -/
def EndpointsCut (lookup : Lookups) (s : Selectors) (index : Fin 136)
 (before middle after : State) (weight : U32) (pf ps cf cs : NQ)
 (passedSelectors : Selectors) (producer consumer : CompiledPoolV1PairForestEndpoint)
 (producerTag consumerTag producerWeight consumerWeight : U32)
 (producerBefore consumerBefore : State) (logEnd next : Nat) : Prop :=
 passedSelectors=s ∧ producer=(NJL_EndpointLookup.link index).producer ∧
 consumer=(NJL_EndpointLookup.link index).consumer ∧
 producerTag=(NJL_EndpointLookup.link index).tag ∧ consumerTag=(NJL_EndpointLookup.link index).tag ∧
 producerWeight=weight ∧ consumerWeight=weight ∧ producerBefore=before ∧ consumerBefore=middle ∧
 logEnd=3 ∧ next=index.val+1 ∧
 NKR_SumCopyCuts.EndpointFrame before middle
  (NJL_EndpointLookup.groupIndex index false (lookup index false))
  (NJL_EndpointLookup.patternIndex index false (lookup index false)) pf ps ∧
 NKR_SumCopyCuts.EndpointFrame middle after
  (NJL_EndpointLookup.groupIndex index true (lookup index true))
  (NJL_EndpointLookup.patternIndex index true (lookup index true)) cf cs

/--Source/nativeG link projection composition at SAME217 reply and both214
prestates. The source proof of CLOSED217's empty mutable footprint permits
splitting the scalar call from the endpoint sequence. -/
theorem compose (lookup : Lookups) (s : Selectors) (index : Fin 136)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (before middle after : State) (weight reply : U32) (pf ps cf cs : NQ)
 (passedLink : CompiledPoolV1PairForestLink) (passedAppend : U64)
 (passedVariant : PoolV1PairForestCompiledVariantV1) (passedSelectors : Selectors)
 (producer consumer : CompiledPoolV1PairForestEndpoint)
 (producerTag consumerTag producerWeight consumerWeight : U32)
 (producerBefore consumerBefore : State) (logEnd next : Nat)
 (w : WeightCut index append variant weight reply passedLink passedAppend passedVariant)
 (e : EndpointsCut lookup s index before middle after reply pf ps cf cs passedSelectors
  producer consumer producerTag consumerTag producerWeight consumerWeight
  producerBefore consumerBefore logEnd next) :
 NKR_SumCopyCuts.LinkCut lookup s index append variant before middle after weight pf ps cf cs
  passedLink passedAppend passedVariant passedSelectors producer consumer
  producerTag consumerTag producerWeight consumerWeight producerBefore consumerBefore logEnd next := by
 rcases w with ⟨hl,ha,hv,hr⟩
 subst reply
 exact ⟨hl,ha,hv,e⟩

#print compose
#print axioms compose
end AspisR1.NKR_SumCopySplitCuts
end
