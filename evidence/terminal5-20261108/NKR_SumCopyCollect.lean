import NJL_EndpointRoot
import NJB_AbortPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyCollect
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIq_Native.pool_v1.pair_forest_copy_terminal
abbrev State := Fin 103 → NQ
abbrev Lookups := ∀ (index : Fin 136) (consumer : Bool),NJL_EndpointLookup.Cut index consumer

/-- One actual218 link: SAME link_weight217 result is passed first to the
producer214 invocation and then the consumer214 invocation on its poststate. -/
def step (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (index : Fin 136) (before : State) : Result State := do
 let weight ← link_weight (NJL_EndpointLookup.link index) append variant
 let middle ← NJL_EndpointRoot.reference before s index false (lookup index false)
  (NJL_EndpointLookup.link index).tag weight
 NJL_EndpointRoot.reference middle s index true (lookup index true)
  (NJL_EndpointLookup.link index).tag weight

def Invocation (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (index : Fin 136) (before after : State) : Prop :=
 ∃ (weight : U32) (middle : State),
 link_weight (NJL_EndpointLookup.link index) append variant=ok weight ∧ weight.val≤1 ∧
 NJL_EndpointRoot.reference before s index false (lookup index false)
  (NJL_EndpointLookup.link index).tag weight=ok middle ∧
 NJL_EndpointRoot.reference middle s index true (lookup index true)
  (NJL_EndpointLookup.link index).tag weight=ok after

theorem step_source (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (index : Fin 136) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after,step lookup append variant s index before=ok after ∧
 Invocation lookup append variant s index before after ∧ ∀ i,Canon (after i) := by
 obtain ⟨weight,weightCall,binary,_⟩ := NJL_EndpointLookup.caller_weight index append variant
 obtain ⟨_,_,_,middle,_,_,_,_,_,middleCall,middleCanon,_⟩ :=
  NJL_EndpointRoot.source before s index false (NJL_EndpointLookup.link index).tag weight
   (lookup index false) hb hs binary
 obtain ⟨_,_,_,after,_,_,_,_,_,afterCall,afterCanon,_⟩ :=
  NJL_EndpointRoot.source middle s index true (NJL_EndpointLookup.link index).tag weight
   (lookup index true) middleCanon hs binary
 refine ⟨after,?_,⟨weight,middle,weightCall,binary,middleCall,afterCall⟩,afterCanon⟩
 simp only [step,weightCall,middleCall,afterCall,bind_tc_ok]

inductive Trace (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) : List (Fin 136) → State → State → Prop
 | nil (before) : Trace lookup append variant s [] before before
 | cons {index rest before middle after} : Invocation lookup append variant s index before middle →
  Trace lookup append variant s rest middle after → Trace lookup append variant s (index::rest) before after

/-- The reviewed lookup bounds are the existing214 native-cut transcription,
not child success or an output assumption. Actual217 binary provenance and
both214 canonical domains are internally established at every one of136links. -/
theorem source (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (indices : List (Fin 136)) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (fun i state=>step lookup append variant s i state) indices before=ok after ∧
 Trace lookup append variant s indices before after ∧ ∀ i,Canon (after i) := by
 induction indices generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb⟩
 | cons index rest ih =>
  obtain ⟨middle,call,inv,cm⟩ := step_source lookup append variant s index before hs hb
  obtain ⟨after,restCall,tr,ca⟩ := ih middle cm
  exact ⟨after,by simp only [NJB_StateUpdates.run,call,restCall,bind_tc_ok],.cons inv tr,ca⟩

#print axioms step_source
#print axioms source
end AspisR1.NKR_SumCopyCollect
end
