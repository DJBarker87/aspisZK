import NKR_SumCopyCollect
import NKR_SumCopyTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKR_SumCopyCollect (State Lookups)
open FIq_Native.pool_v1.pair_forest_copy_terminal

def EndpointFrame (before after : State) (g : Fin 30) (p : Fin 43) (first second : NQ) : Prop :=
 ∀ j,after j=if j=NJL_EndpointIndices.pattern p then second
  else if j=NJL_EndpointIndices.weight g then first else before j

/-- Compose214's two complete declared-footprint frames. The native218 child
oracle writes BOTH actual cells;no partial103-cell seed is substituted. -/
theorem endpoint_frame (before middle after : State) (g : Fin 30) (p : Fin 43) (rhs high first second : NQ)
 (mcut : NJL_EndpointCell.Cut before middle (NJL_EndpointIndices.weight g) rhs first
  ⟨1,before (NJL_EndpointIndices.weight g),rhs⟩ 1)
 (acut : NJL_EndpointCell.Cut middle after (NJL_EndpointIndices.pattern p) high second
  ⟨1,middle (NJL_EndpointIndices.pattern p),high⟩ 1) :
 EndpointFrame before after g p first second := by
 intro j
 rw [acut.2.2.2.2 j]
 by_cases hp : j=NJL_EndpointIndices.pattern p
 · simp only [if_pos hp]
 · simp only [if_neg hp]
   exact mcut.2.2.2.2 j

/-- NKR_copy_link_cut transcription:full217descriptor/append/variant,
producer thenconsumer SAME weight,allselector/scratch input payloads,and
both214 full two-cell footprints threaded on the SAME103-cell state. -/
def LinkCut (lookup : Lookups) (s : Selectors) (index : Fin 136) (append : U64)
 (variant : PoolV1PairForestCompiledVariantV1) (before middle after : State)
 (w : U32) (pfirst psecond cfirst csecond : NQ)
 (passedLink : CompiledPoolV1PairForestLink) (passedAppend : U64)
 (passedVariant : PoolV1PairForestCompiledVariantV1) (passedSelectors : Selectors)
 (passedProducer passedConsumer : CompiledPoolV1PairForestEndpoint)
 (passedProducerTag passedConsumerTag passedProducerWeight passedConsumerWeight : U32)
 (passedProducerBefore passedConsumerBefore : State) (calls next : Nat) : Prop :=
 passedLink=NJL_EndpointLookup.link index ∧ passedAppend=append ∧ passedVariant=variant ∧
 passedSelectors=s ∧ passedProducer=(NJL_EndpointLookup.link index).producer ∧
 passedConsumer=(NJL_EndpointLookup.link index).consumer ∧
 passedProducerTag=(NJL_EndpointLookup.link index).tag ∧ passedConsumerTag=(NJL_EndpointLookup.link index).tag ∧
 passedProducerWeight=w ∧ passedConsumerWeight=w ∧ passedProducerBefore=before ∧ passedConsumerBefore=middle ∧ calls=3 ∧ next=index.val+1 ∧
 EndpointFrame before middle (NJL_EndpointLookup.groupIndex index false (lookup index false))
  (NJL_EndpointLookup.patternIndex index false (lookup index false)) pfirst psecond ∧
 EndpointFrame middle after (NJL_EndpointLookup.groupIndex index true (lookup index true))
  (NJL_EndpointLookup.patternIndex index true (lookup index true)) cfirst csecond

theorem link (lookup : Lookups) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (s : Selectors) (index : Fin 136) (before : State)
 (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,Canon (before i)) :
 ∃ after middle w pfirst psecond cfirst csecond,
 NKR_SumCopyCollect.step lookup append variant s index before=ok after ∧
 link_weight (NJL_EndpointLookup.link index) append variant=ok w ∧
 LinkCut lookup s index append variant before middle after w pfirst psecond cfirst csecond
  (NJL_EndpointLookup.link index) append variant s
  (NJL_EndpointLookup.link index).producer (NJL_EndpointLookup.link index).consumer
  (NJL_EndpointLookup.link index).tag (NJL_EndpointLookup.link index).tag w w before middle 3 (index.val+1) ∧
 ∀ i,Canon (after i) := by
 obtain ⟨w,weightCall,binary,_⟩ := NJL_EndpointLookup.caller_weight index append variant
 obtain ⟨pf,ps,pm,middle,_,_,_,pmcut,pacut,middleCall,middleCanon,_⟩ :=
  NJL_EndpointRoot.source before s index false (NJL_EndpointLookup.link index).tag w
   (lookup index false) hb hs binary
 obtain ⟨cf,cs,cm,after,_,_,_,cmcut,cacut,afterCall,afterCanon,_⟩ :=
  NJL_EndpointRoot.source middle s index true (NJL_EndpointLookup.link index).tag w
   (lookup index true) middleCanon hs binary
 refine ⟨after,middle,w,pf,ps,cf,cs,?_,weightCall,?_,afterCanon⟩
 · simp only [NKR_SumCopyCollect.step,weightCall,middleCall,afterCall,bind_tc_ok]
 · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    endpoint_frame before pm middle _ _ _ _ pf ps pmcut pacut,
    endpoint_frame middle cm after _ _ _ _ cf cs cmcut cacut⟩

/-- NKR_copy_tail_cut returned channels after the actual all8row assignment
and active/residual/product sequence;the root supplies all child Results. -/
def TailCut (values weights : Array NQ 4#usize) (helper chi active residual scaled : NQ)
 (passedRow : CopyRowExtension) (passedHelper passedChi mulLeft mulRight : NQ)
 (out : PoolV1PairForestCompiledCopyTerminalV1) (calls : Nat) : Prop :=
 passedRow=NKR_SumCopyTail.row values weights ∧ passedHelper=helper ∧ passedChi=chi ∧
 mulLeft=active ∧ mulRight=residual ∧ out.active=active ∧ out.residual=scaled ∧ calls=3

#print axioms endpoint_frame
#print axioms link
end AspisR1.NKR_SumCopyCuts
end
