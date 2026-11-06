import NKR_SumSplitCuts
import NKR_SumFinishCohort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishComposed
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NKR_SumFinishData
open NKR_SumFinishBatch (State padded arguments)

/-- ONE actual from_fn callback,with every216 call at its actual
coordinate and all high/low/scratch payloads unchanged. Caller establishes
the216 high canonical domain; inactive callbacks have no child call. -/
theorem tag_source (scratch : Fin 103 → NQ) (s : NKR_SumFinishInvocation.Selectors)
 (b : Fin 9) (i : Fin 4) (hh : FIw_ArrayValue.canonical s.high) :
 ∃ reply,
 NKR_SumSplitCuts.TagCell scratch s (batchStart b) (batchCount b) i reply
  (padded (NKR_SumFinishInvocation.tagValues s) b i)
  (if i.val<batchCount b then 1 else 0) (batchStart b+i.val)
  (NJB_ArrayCarrier.cell s.high) (NJB_ArrayCarrier.cell s.low) scratch ∧
 (∀ h : i.val<batchCount b,
  NJL_TagRoot.reference s (batchCoordinate b ⟨i.val,h⟩)=ok reply) := by
 by_cases hi : i.val<batchCount b
 · let c := batchCoordinate b ⟨i.val,hi⟩
   refine ⟨NKR_SumFinishInvocation.tags s c,?_,?_⟩
   · refine ⟨NKR_SumSplitCuts.batch_domain b,rfl,fun _=>⟨rfl,rfl,rfl,rfl⟩,?_⟩
     simp [padded,hi,c,NKR_SumFinishInvocation.tagValues]
   · intro h
     exact (NKR_SumFinishInvocation.tag_calls s hh c).1
 · refine ⟨FIq_Native.field.QM31.ZERO,?_,?_⟩
   · refine ⟨NKR_SumSplitCuts.batch_domain b,rfl,?_,?_⟩
     · intro h;exact False.elim (hi h)
     · simp [padded,hi]
   · intro h;exact False.elim (hi h)

/-- Pure padding/read bookkeeping. Its source classification remains P7
unless the independent optional data-cell native pair is also replayed. -/
theorem data_source (scratch : Fin 103 → NQ) (s : NKR_SumFinishInvocation.Selectors)
 (b : Fin 9) (i : Fin 4) :
 NKR_SumSplitCuts.DataCell scratch s b i
  (padded (fun c=>scratch (NJL_EndpointIndices.weight c)) b i)
  (padded (fun c=>NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low c)) b i) :=
 ⟨NKR_SumSplitCuts.batch_domain b,rfl,rfl⟩

#print axioms tag_source
#print axioms data_source
/-- Finite4callback construction count. This reduces only source-control
indices,never field values or a large recurrence. Together with tag_source's
arbitrary callback/payload law and array extensionality this composes the
one-iteration primitive into each actual from_fn4 construction. -/
theorem callback_count (b : Fin 9) :
 ((List.finRange 4).map (fun i=>if i.val<batchCount b then (1 : Nat) else 0)).sum=batchCount b := by
 fin_cases b <;> decide

#print axioms callback_count
/-- NEW split arithmetic primitive composed with SAME-argument225/add laws.
The four scalar replies occupy exactly the four chronological call slots.
No retired103cell batch certificate is consumed by this association. -/
def BatchInvocation (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before after : State) : Prop :=
 ∃ v vr w wr,
 NKR_SumCarrier.reference (arguments tags b) (arguments lows b) (batchCount b)=ok v ∧
 FIq_Native.field.QM31.add (before.1 (batchGroup b)) v=ok vr ∧
 NKR_SumCarrier.reference (arguments weights b) (arguments lows b) (batchCount b)=ok w ∧
 FIq_Native.field.QM31.add (before.2 (batchGroup b)) w=ok wr ∧
 NKR_SumSplitCuts.Arithmetic before after (batchGroup b) (batchStart b) (batchCount b)
  (padded tags b) (padded weights b) (padded lows b) ![v,vr,w,wr]
  ![0,1,0,1] ![batchCount b,0,batchCount b,0]
  (fun seek=>![padded tags b seek,before.1 (batchGroup b),padded weights b seek,before.2 (batchGroup b)])
  (fun seek=>![padded lows b seek,v,padded lows b seek,w]) 4 (batchStart b+batchCount b)

/-- Native-G to source:source induction uses precisely the full4+4frames
proved by the NEW arithmetic window. Call-operand/channel equalities remain
in BatchInvocation and are instantiated at exactly these arrays. -/
theorem batch_to_source {tags weights lows : Fin 30 → NQ} {b : Fin 9} {before after : State}
 (h : BatchInvocation tags weights lows b before after) :
 NKR_SumFinishTrace.Invocation tags weights lows b before after := by
 rcases h with ⟨v,vr,w,wr,hv,ha,hw,hwa,cut⟩
 rcases cut with ⟨_,_,_,_,_,_,_,fv,fw⟩
 refine ⟨v,vr,w,wr,hv,ha,hw,hwa,?_⟩
 refine ⟨rfl,rfl,rfl,rfl,fun _=>rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
 · intro i
   simpa [eq_comm] using fv i
 · intro i
   simpa [eq_comm] using fw i

/-- Source-side construction of NEW primitive observations. This is NOT a
native proof:the independent native positive/negative pair supplies the
implementation association for the same projection shape. -/
theorem batch_from_source {tags weights lows : Fin 30 → NQ} {b : Fin 9} {before after : State}
 (h : NKR_SumFinishTrace.Invocation tags weights lows b before after) :
 BatchInvocation tags weights lows b before after := by
 rcases h with ⟨v,vr,w,wr,hv,ha,hw,hwa,cut⟩
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,fv,fw⟩
 refine ⟨v,vr,w,wr,hv,ha,hw,hwa,NKR_SumSplitCuts.batch_domain b,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
 · intro seek;exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 · intro i;simpa [eq_comm] using fv i
 · intro i;simpa [eq_comm] using fw i

/-- NEW pattern primitives:product has no mutable26cell buffer;write has
no103cell scratch. Their only shared channel is the complete product reply.
The emitted pure multiplication law discharges that channel,not Kani. -/
def PatternInvocation (scratch : Fin 103 → NQ) (lows : Fin 16 → NQ)
 (c : Fin 43) (before after : Fin 26 → NQ) : Prop :=
 ∃ product reply,
 FIq_Native.field.QM31.mul (scratch (NKR_SumFinishPattern.scratchIndex c)) (lows (pLow c))=ok product ∧
 FIq_Native.field.QM31.add (before (pOut c)) product=ok reply ∧
 NKR_SumSplitCuts.Product scratch lows c product product
  (scratch (NKR_SumFinishPattern.scratchIndex c)) (lows (pLow c)) (pOut c) 1 ∧
 NKR_SumSplitCuts.Write before after c (pOut c) product reply (before (pOut c)) product 1 (c.val+1)

theorem pattern_to_source {scratch : Fin 103 → NQ} {lows : Fin 16 → NQ}
 {c : Fin 43} {before after : Fin 26 → NQ} (h : PatternInvocation scratch lows c before after) :
 NKR_SumPatternTrace.Invocation scratch lows c before after := by
 rcases h with ⟨p,r,hm,ha,_,write⟩
 rcases write with ⟨_,_,_,_,frame⟩
 refine ⟨p,r,hm,ha,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i;simpa only [eq_comm] using frame i

theorem pattern_from_source {scratch : Fin 103 → NQ} {lows : Fin 16 → NQ}
 {c : Fin 43} {before after : Fin 26 → NQ}
 (h : NKR_SumPatternTrace.Invocation scratch lows c before after) :
 PatternInvocation scratch lows c before after := by
 rcases h with ⟨p,r,hm,ha,cut⟩
 rcases cut with ⟨_,_,_,_,_,_,_,frame⟩
 refine ⟨p,r,hm,ha,⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,?_⟩
 intro i;simpa only [eq_comm] using frame i

inductive BatchTrace (tags weights lows : Fin 30 → NQ) : List (Fin 9) → State → State → Prop
 | nil (s) : BatchTrace tags weights lows [] s s
 | cons {b bs before next after} : BatchInvocation tags weights lows b before next →
   BatchTrace tags weights lows bs next after → BatchTrace tags weights lows (b::bs) before after
inductive PatternTrace (scratch : Fin 103 → NQ) (lows : Fin 16 → NQ) :
 List (Fin 43) → (Fin 26 → NQ) → (Fin 26 → NQ) → Prop
 | nil (s) : PatternTrace scratch lows [] s s
 | cons {c cs before next after} : PatternInvocation scratch lows c before next →
   PatternTrace scratch lows cs next after → PatternTrace scratch lows (c::cs) before after

theorem batch_trace_to_source {tags weights lows : Fin 30 → NQ} {bs : List (Fin 9)} {before after : State}
 (h : BatchTrace tags weights lows bs before after) :
 NKR_SumFinishTrace.Trace tags weights lows bs before after := by
 induction h with
 | nil s=>exact .nil s
 | cons inv _ ih=>exact .cons (batch_to_source inv) ih

theorem batch_trace_from_source {tags weights lows : Fin 30 → NQ} {bs : List (Fin 9)} {before after : State}
 (h : NKR_SumFinishTrace.Trace tags weights lows bs before after) :
 BatchTrace tags weights lows bs before after := by
 induction h with
 | nil s=>exact .nil s
 | cons inv _ ih=>exact .cons (batch_from_source inv) ih

theorem pattern_trace_to_source {scratch : Fin 103 → NQ} {lows : Fin 16 → NQ} {cs : List (Fin 43)} {before after : Fin 26 → NQ}
 (h : PatternTrace scratch lows cs before after) :
 NKR_SumPatternTrace.Trace scratch lows cs before after := by
 induction h with
 | nil s=>exact .nil s
 | cons inv _ ih=>exact .cons (pattern_to_source inv) ih

theorem pattern_trace_from_source {scratch : Fin 103 → NQ} {lows : Fin 16 → NQ} {cs : List (Fin 43)} {before after : Fin 26 → NQ}
 (h : NKR_SumPatternTrace.Trace scratch lows cs before after) :
 PatternTrace scratch lows cs before after := by
 induction h with
 | nil s=>exact .nil s
 | cons inv _ ih=>exact .cons (pattern_from_source inv) ih

/-- Canonical-only220 root. All actual child domains and success channels
come from the existing emitted source proofs; the independent split native
pairs attach through the two forward association lemmas above. This root
never assumes a child success, endpoint equality, or retired native cut. -/
theorem source (scratch : NKR_SumFinishInvocation.Scratch)
 (s : NKR_SumFinishInvocation.Selectors) (terms : NKR_SumFinishInvocation.Patterns)
 (hsc : FIw_ArrayValue.canonical scratch) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (ht : FIw_ArrayValue.canonical terms) :
 ∃ (dot : State) (coefficients : Fin 26 → NQ) (finished : Fin 4 → NQ),
 BatchTrace (NKR_SumFinishInvocation.tagValues s)
  (NKR_SumFinishInvocation.weightValues scratch) (NKR_SumFinishInvocation.lowValues s)
  NKR_SumFinishFold.order (NKR_SumFinishInvocation.zero4,NKR_SumFinishInvocation.zero4) dot ∧
 PatternTrace (NJB_ArrayCarrier.cell scratch) (NJB_ArrayCarrier.cell s.low)
  (List.finRange 43) NKR_SumFinishInvocation.zero26 coefficients ∧
 NKR_SumFinishInvocation.reference scratch s terms=
  ok (NJB_ArrayCarrier.array (N:=4#usize) finished,NJB_ArrayCarrier.array (N:=4#usize) dot.2) ∧
 FIw_ArrayValue.canonical (NJB_ArrayCarrier.array (N:=4#usize) finished) ∧
 FIw_ArrayValue.canonical (NJB_ArrayCarrier.array (N:=4#usize) dot.2) ∧
 (∀ g,FIv_NativeValue.decode (finished g)=NKR_SumFinishCohort.values scratch s terms g) ∧
 (∀ g,FIv_NativeValue.decode (dot.2 g)=NKR_SumFinishCohort.baseWeights scratch s g) := by
 obtain ⟨dot,coefficients,finished,_,_,dt,_,pt,_,_,call,_,_,_,_,_,_⟩ :=
  NKR_SumFinishInvocation.source scratch s terms hsc hh hl ht
 obtain ⟨outV,outW,outCall,cv,cw,vv,ww⟩ :=
  NKR_SumFinishCohort.source scratch s terms hsc hh hl ht
 have same := Result.ok.inj (outCall.symm.trans call)
 have hv : outV=NJB_ArrayCarrier.array (N:=4#usize) finished := congrArg Prod.fst same
 have hw : outW=NJB_ArrayCarrier.array (N:=4#usize) dot.2 := congrArg Prod.snd same
 rw [hv] at cv vv
 rw [hw] at cw ww
 refine ⟨dot,coefficients,finished,batch_trace_from_source dt,pattern_trace_from_source pt,call,cv,cw,?_,?_⟩
 · intro g;simpa only [NJB_ArrayCarrier.cell_array] using vv g
 · intro g;simpa only [NJB_ArrayCarrier.cell_array] using ww g

#print source
#print axioms source
#print axioms batch_to_source
#print axioms batch_from_source
#print axioms pattern_to_source
#print axioms pattern_from_source
#print axioms batch_trace_to_source
#print axioms batch_trace_from_source
#print axioms pattern_trace_to_source
#print axioms pattern_trace_from_source
end AspisR1.NKR_SumFinishComposed
end
