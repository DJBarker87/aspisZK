import NKR_SumFinishMeaning
import NKR_SumFinishPattern
import NJL_TagRoot
import NJL_PatternRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKR_SumFinishBatch (State)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
abbrev Scratch := Array NQ 103#usize
abbrev Patterns := Array NQ 14#usize

def tags (s : Selectors) (c : Fin 30) : NQ :=
 match NJL_TagRoot.reference s c with | ok q=>q | _=>FIq_Native.field.QM31.ZERO

def tagValues (s : Selectors) : Fin 30 → NQ := tags s
def weightValues (scratch : Scratch) (c : Fin 30) : NQ :=
 NJB_ArrayCarrier.cell scratch (NJL_EndpointIndices.weight c)
def lowValues (s : Selectors) (c : Fin 30) : NQ :=
 NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low c)
def zero4 : Fin 4 → NQ := fun _=>FIq_Native.field.QM31.ZERO
def zero26 : Fin 26 → NQ := fun _=>FIq_Native.field.QM31.ZERO

theorem tag_calls (s : Selectors) (hs : FIw_ArrayValue.canonical s.high) :
 ∀ c,NJL_TagRoot.reference s c=ok (tags s c) ∧ Canon (tags s c) ∧
 decode (tags s c)=NJL_TagMeaning.model s (NJL_TagData.indices c) := by
 intro c
 obtain ⟨out,hout,_,_,hc,hv⟩ := NJL_TagRoot.source s c hs
 have tag : tags s c=NJB_Words.value out := by simp only [tags,hout]
 rw [tag]
 exact ⟨hout,hc,hv⟩

def reference (scratch : Scratch) (s : Selectors) (terms : Patterns) : Result (Array NQ 4#usize × Array NQ 4#usize) := do
 let dot ← NKR_SumFinishFold.run (tagValues s) (weightValues scratch) (lowValues s)
  NKR_SumFinishFold.order (zero4,zero4)
 let coefficients ← NJB_StateUpdates.run
  (NKR_SumFinishPattern.step (NJB_ArrayCarrier.cell scratch) (NJB_ArrayCarrier.cell s.low))
  (List.finRange 43) zero26
 let finished ← NJB_PatternReference.reference (NJB_ArrayCarrier.cell terms) coefficients dot.1
 ok (NJB_ArrayCarrier.array finished,NJB_ArrayCarrier.array dot.2)

/-- Complete220 source-ordered invocation relation. The tag216 equations
are instantiated at every actual coordinate, dot batches thread both4-cell
channels, the43-coefficient loop threads the SAME26-cell state, then219
consumes exactly those coefficients/values and returns all4cells plus weights.
Every child Result/domain is discharged internally. -/
theorem source (scratch : Scratch) (s : Selectors) (terms : Patterns)
 (hsc : FIw_ArrayValue.canonical scratch) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (ht : FIw_ArrayValue.canonical terms) :
 ∃ (dot : State) (coefficients : Fin 26 → NQ) (finished : Fin 4 → NQ),
 (∀ c,NJL_TagRoot.reference s c=ok (tags s c) ∧ Canon (tags s c) ∧
  decode (tags s c)=NJL_TagMeaning.model s (NJL_TagData.indices c)) ∧
 NKR_SumFinishFold.run (tagValues s) (weightValues scratch) (lowValues s)
  NKR_SumFinishFold.order (zero4,zero4)=ok dot ∧
 NKR_SumFinishFold.Trace (tagValues s) (weightValues scratch) (lowValues s)
  NKR_SumFinishFold.order (zero4,zero4) dot ∧
 NJB_StateUpdates.run
  (NKR_SumFinishPattern.step (NJB_ArrayCarrier.cell scratch) (NJB_ArrayCarrier.cell s.low))
  (List.finRange 43) zero26=ok coefficients ∧
 NJB_PatternReference.reference (NJB_ArrayCarrier.cell terms) coefficients dot.1=ok finished ∧
 NJL_PatternOuter.Trace (NJB_ArrayCarrier.cell terms) coefficients (List.ofFn (fun g : Fin 4=>g)) dot.1 finished ∧
 reference scratch s terms=ok (NJB_ArrayCarrier.array finished,NJB_ArrayCarrier.array dot.2) ∧
 NKR_SumFinishMeaning.decoded dot=NKR_SumFinishFold.order.foldl
  (fun state b=>NKR_SumFinishMeaning.stepModel (tagValues s) (weightValues scratch) (lowValues s) b state)
  (NKR_SumFinishMeaning.decoded (zero4,zero4)) ∧
 NJB_StateUpdates.decoded coefficients=(List.finRange 43).foldl
  (fun state c=>NKR_SumFinishPattern.modelStep
   (fun i=>decode (NJB_ArrayCarrier.cell scratch i)) (fun i=>decode (NJB_ArrayCarrier.cell s.low i)) c state)
  (NJB_StateUpdates.decoded zero26) ∧
 (∀ i,Canon (finished i)) ∧ (∀ i,Canon (dot.2 i)) ∧
 (∀ g,decode (finished g)=decode (dot.1 g)+NJL_PatternMeaning.dot
  (fun i=>decode (NJB_ArrayCarrier.cell terms i)) (fun i=>decode (coefficients i)) g) := by
 have tc := tag_calls s hh
 have tcanon : ∀ i,Canon (tagValues s i) := fun i=>(tc i).2.1
 have wcanon : ∀ i,Canon (weightValues scratch i) := fun i=>NJB_ArrayCarrier.canonical_cell scratch hsc _
 have lcanon : ∀ i,Canon (lowValues s i) := fun i=>NJB_ArrayCarrier.canonical_cell s.low hl _
 have z4 : ∀ i,Canon (zero4 i) := fun _=>FIv_NativeValue.zero.1
 have z26 : ∀ i,Canon (zero26 i) := fun _=>FIv_NativeValue.zero.1
 obtain ⟨dot,dotCall,dotTrace,dcv,dcw⟩ := NKR_SumFinishFold.source
  (tagValues s) (weightValues scratch) (lowValues s) NKR_SumFinishFold.order (zero4,zero4)
  tcanon wcanon lcanon ⟨z4,z4⟩
 obtain ⟨dotOther,dotOtherCall,_,_,dotValue⟩ := NKR_SumFinishMeaning.source
  (tagValues s) (weightValues scratch) (lowValues s) NKR_SumFinishFold.order (zero4,zero4)
  tcanon wcanon lcanon ⟨z4,z4⟩
 have dotSame : dot=dotOther := Result.ok.inj (dotCall.symm.trans dotOtherCall)
 have dotMeaning := (congrArg NKR_SumFinishMeaning.decoded dotSame).trans dotValue
 obtain ⟨coefficients,coeffCall,cc,coeffValue⟩ := NKR_SumFinishPattern.source
  (NJB_ArrayCarrier.cell scratch) (NJB_ArrayCarrier.cell s.low) (List.finRange 43) zero26
  (NJB_ArrayCarrier.canonical_cell scratch hsc) (NJB_ArrayCarrier.canonical_cell s.low hl) z26
 obtain ⟨finished,finishCall,finishTrace,finishCanon⟩ := NJL_PatternOuter.source
  (NJB_ArrayCarrier.cell terms) coefficients dot.1
  (NJB_ArrayCarrier.canonical_cell terms ht) cc dcv
 obtain ⟨other,otherCall,_,otherValue⟩ := NJB_PatternReference.result
  (NJB_ArrayCarrier.cell terms) coefficients dot.1
  (NJB_ArrayCarrier.canonical_cell terms ht) cc dcv
 have same : finished=other := Result.ok.inj (finishCall.symm.trans otherCall)
 refine ⟨dot,coefficients,finished,tc,dotCall,dotTrace,coeffCall,finishCall,finishTrace,?_,dotMeaning,coeffValue,finishCanon,dcw,?_⟩
 · simp only [reference,dotCall,coeffCall,finishCall,bind_tc_ok]
 · intro g
   rw [same]
   exact (congrFun otherValue g).trans (NJL_PatternMeaning.value _ _ _ g)

#print source
#print axioms tag_calls
#print axioms source
end AspisR1.NKR_SumFinishInvocation
end
