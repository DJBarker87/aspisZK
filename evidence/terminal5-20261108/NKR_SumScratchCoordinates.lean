import NKR_SumCollectMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumScratchCoordinates
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKR_SumCopyCollect (Lookups State)
open FIq_Native.pool_v1.pair_forest_copy_terminal

theorem weight_injective : Function.Injective NJL_EndpointIndices.weight := by
 intro a b h
 apply Fin.ext
 have val:=congrArg Fin.val h
 dsimp only [NJL_EndpointIndices.weight] at val
 omega

theorem pattern_injective : Function.Injective NJL_EndpointIndices.pattern := by
 intro a b h
 apply Fin.ext
 have val:=congrArg Fin.val h
 dsimp only [NJL_EndpointIndices.pattern] at val
 omega

theorem weight_contribution (lookup : Lookups) (s : Selectors) (index : Fin 136) (consumer : Bool)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1) (g : Fin 30) :
 NKR_SumCollectMeaning.contribution lookup s index consumer append variant (NJL_EndpointIndices.weight g)=
 if g=NJL_EndpointLookup.groupIndex index consumer (lookup index consumer) then
 decode (NJL_EndpointLookup.high s index consumer (lookup index consumer))*NKR_SumCollectMeaning.weight index append variant else 0 := by
 unfold NKR_SumCollectMeaning.contribution
 by_cases same : g=NJL_EndpointLookup.groupIndex index consumer (lookup index consumer)
 · subst g
   simp only [if_true]
 · have different := fun h=>same (weight_injective h)
   simp only [if_neg different,if_neg same,if_neg (NJL_EndpointIndices.disjoint _ _)]

theorem pattern_contribution (lookup : Lookups) (s : Selectors) (index : Fin 136) (consumer : Bool)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1) (p : Fin 43) :
 NKR_SumCollectMeaning.contribution lookup s index consumer append variant (NJL_EndpointIndices.pattern p)=
 if p=NJL_EndpointLookup.patternIndex index consumer (lookup index consumer) then
 decode (NJL_EndpointLookup.high s index consumer (lookup index consumer)) else 0 := by
 unfold NKR_SumCollectMeaning.contribution
 simp only [if_neg (Ne.symm (NJL_EndpointIndices.disjoint _ _))]
 by_cases same : p=NJL_EndpointLookup.patternIndex index consumer (lookup index consumer)
 · subst p
   simp only [if_true]
 · have different := fun h=>same (pattern_injective h)
   simp only [if_neg different,if_neg same]

/-- Actual30weight/43pattern scratch coordinates as endpoint-indexed sums.
This discharges the sparse support before any source136loop is concretized. -/
theorem source (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (indices : List (Fin 136)) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state) indices before=ok after ∧
 (∀ i,Canon (after i)) ∧
 (∀ g,decode (after (NJL_EndpointIndices.weight g))=decode (before (NJL_EndpointIndices.weight g))+
  (indices.map (fun i=>(if g=NJL_EndpointLookup.groupIndex i false (lookup i false) then
   decode (NJL_EndpointLookup.high s i false (lookup i false))*NKR_SumCollectMeaning.weight i append variant else 0)+
   (if g=NJL_EndpointLookup.groupIndex i true (lookup i true) then
   decode (NJL_EndpointLookup.high s i true (lookup i true))*NKR_SumCollectMeaning.weight i append variant else 0))).sum) ∧
 (∀ p,decode (after (NJL_EndpointIndices.pattern p))=decode (before (NJL_EndpointIndices.pattern p))+
  (indices.map (fun i=>(if p=NJL_EndpointLookup.patternIndex i false (lookup i false) then
   decode (NJL_EndpointLookup.high s i false (lookup i false)) else 0)+
   (if p=NJL_EndpointLookup.patternIndex i true (lookup i true) then
   decode (NJL_EndpointLookup.high s i true (lookup i true)) else 0))).sum) := by
 obtain ⟨after,call,ca,value⟩ := NKR_SumCollectMeaning.source lookup append variant s indices before hs hb
 refine ⟨after,call,ca,?_,?_⟩
 · intro g
   rw [value]
   apply congrArg (fun x=>decode (before (NJL_EndpointIndices.weight g))+x)
   apply congrArg List.sum
   apply List.map_congr_left
   intro i hi
   simp only [NKR_SumCollectMeaning.delta,weight_contribution]
 · intro p
   rw [value]
   apply congrArg (fun x=>decode (before (NJL_EndpointIndices.pattern p))+x)
   apply congrArg List.sum
   apply List.map_congr_left
   intro i hi
   simp only [NKR_SumCollectMeaning.delta,pattern_contribution]

#print axioms weight_injective
#print axioms pattern_injective
#print axioms weight_contribution
#print axioms pattern_contribution
#print axioms source
end AspisR1.NKR_SumScratchCoordinates
end
