import NKR_SumCopyCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCollectMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NKR_SumCopyCollect (Lookups State)

def weight (index : Fin 136) (append : U64) (variant : PoolV1PairForestCompiledVariantV1) : K :=
 R0P.copyLinkWeight (FJk_CopyDescriptor.link (NJL_EndpointLookup.link index)) append.val (FJk_CopyDescriptor.variant variant)

def contribution (lookup : Lookups) (s : Selectors) (index : Fin 136) (consumer : Bool)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1) (j : Fin 103) : K :=
 let g := NJL_EndpointLookup.groupIndex index consumer (lookup index consumer)
 let p := NJL_EndpointLookup.patternIndex index consumer (lookup index consumer)
 let high := NJL_EndpointLookup.high s index consumer (lookup index consumer)
 if j=NJL_EndpointIndices.weight g then decode high*weight index append variant
 else if j=NJL_EndpointIndices.pattern p then decode high else 0

def delta (lookup : Lookups) (s : Selectors) (index : Fin 136)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1) (j : Fin 103) : K :=
 contribution lookup s index false append variant j+contribution lookup s index true append variant j

theorem step_source (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (index : Fin 136) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after,NKR_SumCopyCollect.step lookup append variant s index before=ok after ∧
 (∀ i,Canon (after i)) ∧
 ∀ j,decode (after j)=decode (before j)+delta lookup s index append variant j := by
 obtain ⟨w,weightCall,binary,weightValue⟩ := NJL_EndpointLookup.caller_weight index append variant
 obtain ⟨_,_,_,middle,_,_,_,_,_,middleCall,middleCanon,middleValue⟩ :=
  NJL_EndpointRoot.source before s index false (NJL_EndpointLookup.link index).tag w
   (lookup index false) hb hs binary
 obtain ⟨_,_,_,after,_,_,_,_,_,afterCall,afterCanon,afterValue⟩ :=
  NJL_EndpointRoot.source middle s index true (NJL_EndpointLookup.link index).tag w
   (lookup index true) middleCanon hs binary
 have ep (consumer : Bool) (old new : State)
  (value : ∀ j,decode (new j)=if j=NJL_EndpointIndices.weight (NJL_EndpointLookup.groupIndex index consumer (lookup index consumer)) then
   decode (old j)+decode (NJL_EndpointLookup.high s index consumer (lookup index consumer))*(w.val : K)
   else if j=NJL_EndpointIndices.pattern (NJL_EndpointLookup.patternIndex index consumer (lookup index consumer)) then
   decode (old j)+decode (NJL_EndpointLookup.high s index consumer (lookup index consumer)) else decode (old j)) :
  ∀ j,decode (new j)=decode (old j)+contribution lookup s index consumer append variant j := by
   intro j
   rw [value j]
   dsimp only [contribution]
   rw [weightValue]
   by_cases h1 : j=NJL_EndpointIndices.weight (NJL_EndpointLookup.groupIndex index consumer (lookup index consumer))
   · simp only [if_pos h1]
   · simp only [if_neg h1]
     by_cases h2 : j=NJL_EndpointIndices.pattern (NJL_EndpointLookup.patternIndex index consumer (lookup index consumer))
     · simp only [if_pos h2]
     · simp only [if_neg h2,add_zero]
 refine ⟨after,?_,afterCanon,?_⟩
 · simp only [NKR_SumCopyCollect.step,weightCall,middleCall,afterCall,bind_tc_ok]
 · intro j
   rw [ep true middle after afterValue j,ep false before middle middleValue j]
   unfold delta
   ring

/-- All103scratch cells,including initially-unused tag slots,are exactly the
sum of the actual producer/consumer contributions of the136-link stream.
This is symbolic induction,not concrete field recurrence normalization. -/
theorem source (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (indices : List (Fin 136)) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state) indices before=ok after ∧
 (∀ i,Canon (after i)) ∧
 ∀ j,decode (after j)=decode (before j)+(indices.map (fun i=>delta lookup s i append variant j)).sum := by
 induction indices generalizing before with
 | nil => exact ⟨before,rfl,hb,by intro j;simp⟩
 | cons index rest ih =>
  obtain ⟨middle,call,cm,vm⟩ := step_source lookup append variant s index before hs hb
  obtain ⟨after,restCall,ca,va⟩ := ih middle cm
  refine ⟨after,?_,ca,?_⟩
  · simp only [NJB_StateUpdates.run,call,restCall,bind_tc_ok]
  · intro j
    rw [va,vm]
    simp only [List.map_cons,List.sum_cons]
    ring

#print axioms step_source
#print axioms source
end AspisR1.NKR_SumCollectMeaning
end
