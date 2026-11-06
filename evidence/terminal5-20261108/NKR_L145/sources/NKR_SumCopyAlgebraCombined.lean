import NKR_SumCopyCollect
import NKR_SumFinishData
import NJL_EndpointLookup
import RPv_FJk_CopyStep
import NJL_TagData
import NJL_TagMeaning
import NJL_ActiveInvocation
import NJB_CopyResidual
import NKR_SumFinishInvocation
import NJX_PatternRoot

/- Original helper NKR_SumCollectMeaning.lean; retained source SHA256 0fb5a484375572d1d80e9bb2e980fed7e4a3e26a0806e8900cdee7d5240bc23e -/
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
   · simp only [if_pos h1,weight]
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

/- Original helper NKR_SumLookupCertificate.lean; retained source SHA256 1c21197d1b91f80b83c4a2c9805ce8206a6c5ace7c53d7c6996474d799d5e1f0 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumLookupCertificate
open NKR_SumFinishData

/-- The additional metadata assertions ALREADY proved by
NJL_endpoint_lookup_cut(NJL_control.rs.txt,lines107..114):the exactgc/pc
values equal the source-key scans at the genuine endpoint group/local/pattern.
This is an(ai)(5) reviewed native cut,not any execution/field endpoint.
The main certificate must pin/revalidate that existing native pair. -/
def Cut (index : Fin 136) (consumer : Bool) : Prop :=
 NJL_EndpointLookup.gc index consumer=NJL_EndpointLookup.scanFrom
  (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer) NJL_EndpointLookup.groupKeys 0 ∧
 NJL_EndpointLookup.pc index consumer=NJL_EndpointLookup.scanFrom
  (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,
   NJL_EndpointLookup.column index consumer) NJL_EndpointLookup.patternKeys 0

theorem scan_found {A : Type} [DecidableEq A] (key : A) (xs : List A) (start : Nat)
 (bounded : start+xs.length≤255) (found : NJL_EndpointLookup.scanFrom key xs start<255) :
 ∃ (i : Fin xs.length),NJL_EndpointLookup.scanFrom key xs start=start+i.val ∧ xs[i.val]=key := by
 induction xs generalizing start with
 | nil => simp only [NJL_EndpointLookup.scanFrom] at found;omega
 | cons x xs ih =>
  by_cases same : key=x
  · refine ⟨⟨0,by simp⟩,?_,?_⟩
    · simp only [NJL_EndpointLookup.scanFrom,if_pos same,Nat.add_zero]
    · exact same.symm
  · have tailFound : NJL_EndpointLookup.scanFrom key xs (start+1)<255 := by
     simpa only [NJL_EndpointLookup.scanFrom,if_neg same] using found
    obtain ⟨i,scan,read⟩ := ih (start+1) (by simp only [List.length_cons] at bounded;omega) tailFound
    refine ⟨⟨i.val+1,by have:=i.isLt;simp only [List.length_cons];omega⟩,?_,?_⟩
    · simp only [NJL_EndpointLookup.scanFrom,if_neg same,scan]
      omega
    · simpa only [List.getElem_cons_succ] using read

def patternGroup : Fin 43 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3]

theorem group_length : NJL_EndpointLookup.groupKeys.length=30 := by decide
theorem pattern_length : NJL_EndpointLookup.patternKeys.length=43 := by decide

theorem group_key (c : Fin 30) : NJL_EndpointLookup.groupKeys[c.val]'(by rw [group_length];exact c.isLt)=
 ((group c).val,(low c).val) := by fin_cases c <;> rfl

theorem pattern_key (c : Fin 43) : NJL_EndpointLookup.patternKeys[c.val]'(by rw [pattern_length];exact c.isLt)=
 ((patternGroup c).val,(NJB_PatternReference.pattern (pOut c)).val,(pLow c).val) := by fin_cases c <;> rfl

theorem column_mod (index : Fin 136) (consumer : Bool) :
 NJL_EndpointLookup.column index consumer=NJL_EndpointLookup.row index consumer%16 := by
 exact Nat.and_two_pow_sub_one_eq_mod (NJL_EndpointLookup.row index consumer) 4

/-- A symbolic scan proof derives exact endpoint-key associations without
normalizing the136-link registry or inventing a new native assertion. -/
theorem keys (index : Fin 136) (consumer : Bool) (bounds : NJL_EndpointLookup.Cut index consumer)
 (cut : Cut index consumer) :
 ((group (NJL_EndpointLookup.groupIndex index consumer bounds)).val,
  (low (NJL_EndpointLookup.groupIndex index consumer bounds)).val)=
 (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer) ∧
 ((patternGroup (NJL_EndpointLookup.patternIndex index consumer bounds)).val,
  (NJB_PatternReference.pattern (pOut (NJL_EndpointLookup.patternIndex index consumer bounds))).val,
  (pLow (NJL_EndpointLookup.patternIndex index consumer bounds)).val)=
 (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,
  NJL_EndpointLookup.column index consumer) := by
 obtain ⟨g,hg,vg⟩ := scan_found
  (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer)
  NJL_EndpointLookup.groupKeys 0 (by rw [group_length];decide) (by rw [←cut.1];have:=bounds.2.1;omega)
 obtain ⟨p,hp,vp⟩ := scan_found
  (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,NJL_EndpointLookup.column index consumer)
  NJL_EndpointLookup.patternKeys 0 (by rw [pattern_length];decide) (by rw [←cut.2];have:=bounds.2.2;omega)
 have gi : g.val=NJL_EndpointLookup.gc index consumer := by rw [cut.1,hg];omega
 have pi : p.val=NJL_EndpointLookup.pc index consumer := by rw [cut.2,hp];omega
 constructor
 · have v := vg
   have eq : g.val=(NJL_EndpointLookup.groupIndex index consumer bounds).val := gi
   rw [eq,group_key] at v
   exact v
 · have v := vp
   have eq : p.val=(NJL_EndpointLookup.patternIndex index consumer bounds).val := pi
   rw [eq,pattern_key] at v
   exact v

#print axioms scan_found
#print axioms group_length
#print axioms pattern_length
#print axioms group_key
#print axioms pattern_key
#print axioms column_mod
#print axioms keys
end AspisR1.NKR_SumLookupCertificate
end

/- Original helper NKR_SumRegroup.lean; retained source SHA256 2e80982b77d28a05ddf20d256a4c255166b07f715203f425fcc2f02dd3a2e1e1 -/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumRegroup
open FIv_NativeValue (K)
open NKR_SumFinishData

/-- Generic finite sparse-basis contraction. The proof exchanges finite sums
symbolically;no concrete136/272-entry arithmetic term is normalized. -/
theorem contraction {C P : Type} [Fintype C] [Fintype P] [DecidableEq P]
 (out : C → P) (inside : P → Prop) [DecidablePred inside] (term : P → K) (value : C → K) :
 (∑ p : P,if inside p then term p*(∑ c : C,if out c=p then value c else 0) else 0)=
 ∑ c : C,if inside (out c) then term (out c)*value c else 0 := by
 calc
  _=(∑ p : P,∑ c : C,if p=out c then (if inside p then term p*value c else 0) else 0) := by
   apply Finset.sum_congr rfl
   intro p hp
   by_cases h : inside p
   · simp only [if_pos h,Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro c hc
     by_cases equal : out c=p
     · rw [equal]
       simp only [if_true]
     · simp only [if_neg equal,if_neg (Ne.symm equal),mul_zero]
   · simp only [if_neg h]
     symm
     apply Finset.sum_eq_zero
     intro c hc
     split <;> rfl
  _=(∑ c : C,∑ p : P,if p=out c then (if inside p then term p*value c else 0) else 0) := Finset.sum_comm
  _=_ := by
   apply Finset.sum_congr rfl
   intro c hc
   simp

/-- Algebra at each actual endpoint:the high/low selector multiplies BOTH
the tag and compressed pattern;weights independently carry the217binary law. -/
theorem endpoint (high low tag pattern weight : K) :
 high*low*(tag+pattern)=high*tag*low+pattern*(high*low) ∧
 (high*weight)*low=(high*low)*weight := by constructor <;> ring

/--43metadata facts,each only a small index/bound computation. -/
theorem bucket (c : Fin 43) : pOut c∈NJB_PatternReference.coordinates (NKR_SumLookupCertificate.patternGroup c) := by
 fin_cases c <;> decide

theorem bucket_unique (g h : Fin 4) (p : Fin 26)
 (hg : p∈NJB_PatternReference.coordinates g) (hh : p∈NJB_PatternReference.coordinates h) : g=h := by
 have bg : NJB_PatternReference.offset g.castSucc≤p.val ∧ p.val<NJB_PatternReference.offset g.succ := by
  exact of_decide_eq_true (List.mem_filter.mp hg).2
 have bh : NJB_PatternReference.offset h.castSucc≤p.val ∧ p.val<NJB_PatternReference.offset h.succ := by
  exact of_decide_eq_true (List.mem_filter.mp hh).2
 fin_cases g <;> fin_cases h <;> norm_num [NJB_PatternReference.offset] at bg bh ⊢ <;> omega

theorem bucket_iff (g : Fin 4) (c : Fin 43) :
 pOut c∈NJB_PatternReference.coordinates g ↔ NKR_SumLookupCertificate.patternGroup c=g := by
 constructor
 · intro h
   exact bucket_unique _ _ _ (bucket c) h
 · intro h
   rw [←h]
   exact bucket c

#print axioms contraction
#print axioms endpoint
#print axioms bucket
#print axioms bucket_unique
#print axioms bucket_iff
end AspisR1.NKR_SumRegroup
end

/- Original helper NKR_SumTensorAlgebra.lean; retained source SHA256 1b882f35b7e8528d0a9bccc981381317e1054d177157eb667ac77bbffb18a4a9 -/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTensorAlgebra
open FIv_NativeValue (K)

/-- The two physical endpoint channels share the SAME coefficient basis.
This specializes sparse contraction to producer+consumer source136sums,
without evaluating any actual registry or recurrence. -/
theorem contraction_two {C P : Type} [Fintype C] [Fintype P] [DecidableEq P]
 (out0 out1 : C → P) (inside : P → Prop) [DecidablePred inside]
 (term : P → K) (value0 value1 : C → K) :
 (∑ p : P,if inside p then term p*(∑ c : C,
  (if out0 c=p then value0 c else 0)+(if out1 c=p then value1 c else 0)) else 0)=
 ∑ c : C,(if inside (out0 c) then term (out0 c)*value0 c else 0)+
  (if inside (out1 c) then term (out1 c)*value1 c else 0) := by
 calc
  _=(∑ p : P,if inside p then term p*(∑ c : C,if out0 c=p then value0 c else 0) else 0)+
    (∑ p : P,if inside p then term p*(∑ c : C,if out1 c=p then value1 c else 0) else 0) := by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro p hp
   by_cases h : inside p <;> simp [h,Finset.sum_add_distrib,mul_add]
  _=_ := by
   rw [NKR_SumRegroup.contraction,NKR_SumRegroup.contraction,Finset.sum_add_distrib]

#print axioms contraction_two
end AspisR1.NKR_SumTensorAlgebra
end

/- Original helper NKR_SumLegacyRows.lean; retained source SHA256 87c9ebd2846da1be6acbe0d07ed6c71d7c4b9e083e15f014ac26fa250298e964 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumLegacyRows
open FIv_NativeValue (K)

def values (row : R0P.CopyRowExtension K) (g : Fin 4) : K :=
 if h : g.val<2 then row.producerValues ⟨g.val,h⟩
 else row.consumerValues ⟨g.val-2,by have:=g.isLt;omega⟩
def weights (row : R0P.CopyRowExtension K) (g : Fin 4) : K :=
 if h : g.val<2 then row.producerWeights ⟨g.val,h⟩
 else row.consumerWeights ⟨g.val-2,by have:=g.isLt;omega⟩
def group (consumer : Bool) (e : R0P.CopyEndpoint) : Fin 4 :=
 ⟨e.slot.val+(if consumer then 2 else 0),by have:=e.slot.isLt;split <;>omega⟩
def endpoint (link : R0P.CopyLink) (consumer : Bool) : R0P.CopyEndpoint :=
 if consumer then link.consumer else link.producer
def valueTerm (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (link : R0P.CopyLink) (consumer : Bool) : K :=
 let e := endpoint link consumer
 R0P.copySelectorRow s e.row*((link.tag : K)+patterns e.pattern)
def weightTerm (s : R0P.CopySelectors K) (append : Nat) (variant : R0P.Variant)
 (link : R0P.CopyLink) (consumer : Bool) : K :=
 let e := endpoint link consumer
 R0P.copySelectorRow s e.row*R0P.copyLinkWeight link append variant

theorem one_value (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (link : R0P.CopyLink) (g : Fin 4) :
 values (FJk_CopyStep.step s patterns append variant row link) g=values row g+
 (if g=group false link.producer then valueTerm s patterns link false else 0)+
 (if g=group true link.consumer then valueTerm s patterns link true else 0) := by
 cases link with
 | mk tag kind level producer consumer =>
  cases producer with
  | mk pr ps pp =>
   cases consumer with
   | mk cr cs cp =>
    fin_cases ps <;> fin_cases cs <;> fin_cases g <;>
     simp [values,FJk_CopyStep.step,R0P.copyAccumulateEndpoint,group,valueTerm,endpoint,Function.update_apply] <;> ring

theorem one_weight (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (link : R0P.CopyLink) (g : Fin 4) :
 weights (FJk_CopyStep.step s patterns append variant row link) g=weights row g+
 (if g=group false link.producer then weightTerm s append variant link false else 0)+
 (if g=group true link.consumer then weightTerm s append variant link true else 0) := by
 cases link with
 | mk tag kind level producer consumer =>
  cases producer with
  | mk pr ps pp =>
   cases consumer with
   | mk cr cs cp =>
    fin_cases ps <;> fin_cases cs <;> fin_cases g <;>
     simp [weights,FJk_CopyStep.step,R0P.copyAccumulateEndpoint,group,weightTerm,endpoint,Function.update_apply] <;> ring

/-- Symbolic legacy/cohort rowfold over arbitrary link lists. This makes the
final218join an equality of explicit endpoint sums,not two opaque loops. -/
theorem fold_values (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (links : List R0P.CopyLink) (g : Fin 4) :
 values (links.foldl (FJk_CopyStep.step s patterns append variant) row) g=values row g+
 (links.map (fun link=>(if g=group false link.producer then valueTerm s patterns link false else 0)+
 (if g=group true link.consumer then valueTerm s patterns link true else 0))).sum := by
 induction links generalizing row with
 | nil => simp
 | cons link links ih =>
  rw [List.foldl_cons,ih,one_value]
  simp only [List.map_cons,List.sum_cons]
  ring

theorem fold_weights (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (links : List R0P.CopyLink) (g : Fin 4) :
 weights (links.foldl (FJk_CopyStep.step s patterns append variant) row) g=weights row g+
 (links.map (fun link=>(if g=group false link.producer then weightTerm s append variant link false else 0)+
 (if g=group true link.consumer then weightTerm s append variant link true else 0))).sum := by
 induction links generalizing row with
 | nil => simp
 | cons link links ih =>
  rw [List.foldl_cons,ih,one_weight]
  simp only [List.map_cons,List.sum_cons]
  ring

#print axioms one_value
#print axioms one_weight
#print axioms fold_values
#print axioms fold_weights
end AspisR1.NKR_SumLegacyRows
end

/- Original helper NKR_SumIntervals.lean; retained source SHA256 0669b38c877083b1053208f3279bb7229825449da4869c5266e98b3d24790f59 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumIntervals

def intervals (off : Nat → Nat) (n : Nat) : List Nat :=
 (List.range n).flatMap (fun c=>List.range' (off c) (off (c+1)-off c))

theorem partition (off : Nat → Nat) (mono : Monotone off) (n : Nat) :
 intervals off n=List.range' (off 0) (off n-off 0) := by
 induction n with
 | zero => simp [intervals]
 | succ n ih =>
  have first : off 0≤off n := mono (Nat.zero_le n)
  have next : off n≤off (n+1) := mono (Nat.le_succ n)
  have start : off 0+(off n-off 0)=off n := by omega
  have length : (off n-off 0)+(off (n+1)-off n)=off (n+1)-off 0 := by omega
  simp only [intervals,List.range_succ,List.flatMap_append,List.flatMap_singleton] at ih ⊢
  rw [ih]
  have second : List.range' (off n) (off (n+1)-off n)=
   List.range' (off 0+(off n-off 0)) (off (n+1)-off n) :=
   congrArg (fun a=>List.range' a (off (n+1)-off n)) start.symm
  rw [second]
  first
  | rw [←List.range'_append,length]
  | rw [List.range'_append,length]

def off (n : Nat) : Nat := NJL_TagData.offsets ⟨min n 30,by omega⟩

theorem step (n : Nat) : off n≤off (n+1) := by
 by_cases small : n<30
 · have h := (NJL_TagData.interval ⟨n,small⟩).1.le
   simpa only [off,Nat.min_eq_left (Nat.le_of_lt small),Nat.min_eq_left (by omega),
    NJL_TagData.first,NJL_TagData.last] using h
 · have hn : 30≤n := by omega
   have hn' : 30≤n+1 := by omega
   simp only [off,Nat.min_eq_right hn,Nat.min_eq_right hn']

theorem monotone : Monotone off := by
 intro i j hij
 induction j,hij using Nat.le_induction with
 | base => exact Nat.le_refl _
 | succ j hij ih => exact ih.trans (step j)

theorem thirty : intervals off 30=List.range 272 := by
 rw [partition off monotone]
 rfl

/-- Generic map/flatMap laws keep the272positions symbolic. -/
theorem map_flatMap {A B C : Type} (f : A → List B) (v : B → C) (xs : List A) :
 (xs.flatMap f).map v=xs.flatMap (fun a=>(f a).map v) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.flatMap_cons,List.map_append,ih]

theorem fin_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

theorem lists_ext {n : Nat} (xs ys : List (Fin n)) (h : xs.map Fin.val=ys.map Fin.val) : xs=ys := by
 induction xs generalizing ys with
 | nil =>
  cases ys with
  | nil => rfl
  | cons y ys => simp at h
 | cons x xs ih =>
  cases ys with
  | nil => simp at h
  | cons y ys =>
   simp only [List.map_cons,List.cons.injEq] at h
   have xy : x=y := Fin.ext h.1
   subst y
   exact congrArg (List.cons x) (ih ys h.2)

#print axioms partition
#print axioms step
#print axioms monotone
#print axioms thirty
#print axioms map_flatMap
#print axioms fin_values
#print axioms lists_ext
end AspisR1.NKR_SumIntervals
end

/- Original helper NKR_SumTagPartition.lean; retained source SHA256 778ea30dda1f4de07cc0cc6c936c5c601779d5017e5482672eb45f10037258b9 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagPartition
open NKR_SumIntervals

theorem first (c : Fin 30) : NJL_TagData.first c=off c.val := by
 have h : c.val≤30 := Nat.le_of_lt c.isLt
 simp only [off,Nat.min_eq_left h,NJL_TagData.first]
 rfl

theorem last (c : Fin 30) : NJL_TagData.last c=off (c.val+1) := by
 have h : c.val+1≤30 := c.isLt
 simp only [off,Nat.min_eq_left h,NJL_TagData.last]
 rfl

theorem flatMap_map {A B C : Type} (f : B → List C) (v : A → B) (xs : List A) :
 (xs.map v).flatMap f=xs.flatMap (fun a=>f (v a)) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.map_cons,List.flatMap_cons,ih]

/-- The30frozen contiguous buckets cover all272tag terms exactly once.
Proof uses generic range concatenation and Fin.val injectivity,never a
concrete272-cell kernel enumeration. -/
theorem source : (List.finRange 30).flatMap NJL_TagData.indices=List.finRange 272 := by
 apply lists_ext
 rw [map_flatMap]
 have ranges : (List.finRange 30).flatMap (fun c=>(NJL_TagData.indices c).map Fin.val)=intervals off 30 := by
  unfold intervals
  rw [←fin_values 30,flatMap_map]
  apply congrArg (fun f : Fin 30 → List Nat=>(List.finRange 30).flatMap f)
  funext c
  rw [NJL_TagData.range_values,first,last]
 rw [ranges,thirty,fin_values]

#print axioms first
#print axioms last
#print axioms flatMap_map
#print axioms source
end AspisR1.NKR_SumTagPartition
end

/- Original helper NKR_SumTagPermutation.lean; retained source SHA256 62cc0e94baaf2a9922678855a15526ccd7dddd706379fee8d9f6ecf68eee05e9 -/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagPermutation
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
def base : Nat := 1124073472
def tag (t : Fin 272) : Nat := (NJL_TagData.tag t).val
def side (t : Fin 272) : Bool := decide (136≤t.val)
/-- Exact tag-domain assertion in NKR_tag_metadata_cut. -/
def Domain : Prop := ∀ t,base≤tag t ∧ tag t<base+136
/-- Exact NKR_tag_permutation_cut assertion:two fixed-registry positions with
SAME tag and producer/consumer side are identical. This is a reviewed native
constant-metadata cut,not a field/output/cohort equality. -/
def Cut : Prop := ∀ (t u : Fin 272),tag t=tag u → side t=side u → t=u

def index (domain : Domain) (t : Fin 272) : Fin 136 :=
 ⟨tag t-base,by have h:=domain t;omega⟩
def encoded (domain : Domain) (t : Fin 272) : Fin 272 :=
 ⟨(index domain t).val+(if side t then 136 else 0),by
   have h:=(index domain t).isLt
   split <;> omega⟩

theorem injective (domain : Domain) (cut : Cut) : Function.Injective (encoded domain) := by
 intro t u eq
 have val := congrArg Fin.val eq
 change (index domain t).val+(if side t then 136 else 0)=
  (index domain u).val+(if side u then 136 else 0) at val
 have ht:=(index domain t).isLt
 have hu:=(index domain u).isLt
 have st : side t=side u := by
  cases hst : side t <;> cases hsu : side u <;> simp only [hst,hsu,if_true,if_false,Bool.false_eq_true,Bool.true_eq_true] at val ⊢ <;> omega
 have vals : (index domain t).val=(index domain u).val := by rw [st] at val;omega
 have tags : tag t=tag u := by
  change tag t-base=tag u-base at vals
  have dt:=domain t
  have du:=domain u
  omega
 exact cut t u tags st

/-- Finite self-map pigeonhole:272registry positions cover exactly the
136producer plus136consumer source entries. No272-cell kernel replay. -/
theorem surjective (domain : Domain) (cut : Cut) : Function.Surjective (encoded domain) :=
 Finite.surjective_of_injective (encoded domain) (injective domain cut)

theorem sum_transport (domain : Domain) (cut : Cut) (f : Fin 272 → K) :
 ((List.finRange 272).map (fun t=>f (encoded domain t))).sum=((List.finRange 272).map f).sum := by
 change ((List.ofFn (fun t : Fin 272=>t)).map (fun t=>f (encoded domain t))).sum=
  ((List.ofFn (fun t : Fin 272=>t)).map f).sum
 simp only [List.map_ofFn,List.sum_ofFn]
 refine Finset.sum_bij (fun t _=>encoded domain t) ?_ ?_ ?_ ?_
 · intro t ht
   exact Finset.mem_univ _
 · intro t ht u hu eq
   exact injective domain cut eq
 · intro u hu
   obtain ⟨t,eq⟩ := surjective domain cut u
   exact ⟨t,Finset.mem_univ _,eq⟩
 · intro t ht
   rfl

#print axioms injective
#print axioms surjective
#print axioms sum_transport
end AspisR1.NKR_SumTagPermutation
end

/- Original helper NKR_SumTagAssociation.lean; retained source SHA256 d65fea94ef463a0f3bdda0477f6b53b031a284a8fd62752876af2d206b97e172 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagAssociation
open Aeneas Aeneas.Std
open FIv_NativeValue (K decode)
open NKR_SumTagPermutation (Domain index side tag)
open NKR_SumCopyCollect (Lookups)

/-- Remaining exact assertions of NKR_tag_metadata_cut,transcribed on the
model's pinned tag/descriptor arrays. The oldNJLtagregistry cut binds those
arrays to frozen constants and the oldNJLlookup cut binds gc to actualsource
lookup. No field value or composed endpoint equality is asserted here. -/
structure Cut (domain : Domain) : Prop where
 tag : ∀ t,NKR_SumTagPermutation.tag t=(NJL_EndpointLookup.link (index domain t)).tag.val
 block : ∀ t,(NJL_TagData.block t).val=NJL_EndpointLookup.row (index domain t) (side t)/16
 coordinate : ∀ (c : Fin 30) (t : Fin 272),t∈NJL_TagData.indices c →
  NJL_EndpointLookup.gc (index domain t) (side t)=c.val

theorem high (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (t : Fin 272) :
 NJB_ActiveReference.high s (NJL_TagData.block t)=
 NJL_EndpointLookup.high s (index domain t) (side t) (lookup (index domain t) (side t)) := by
 have block : NJL_TagData.block t=NJL_EndpointLookup.block (index domain t) (side t)
  (lookup (index domain t) (side t)) := Fin.ext (cut.block t)
 exact congrArg (NJB_ActiveReference.high s) block

theorem term (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (t : Fin 272) :
 decode (NJB_ActiveReference.high s (NJL_TagData.block t))*(NJL_TagData.tag t).val=
 decode (NJL_EndpointLookup.high s (index domain t) (side t) (lookup (index domain t) (side t)))*
 (NJL_EndpointLookup.link (index domain t)).tag.val := by
 rw [high domain cut lookup s t]
 have value := cut.tag t
 change (NJL_TagData.tag t).val=_ at value
 rw [value]

theorem coordinate (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (c : Fin 30) (t : Fin 272) (ht : t∈NJL_TagData.indices c) :
 NJL_EndpointLookup.groupIndex (index domain t) (side t) (lookup (index domain t) (side t))=c :=
 Fin.ext (cut.coordinate c t ht)

/-- The actual low-selector index of each frozen tag term is its endpoint's
row&15 (equivalentlyrow%16),derived from the reviewed scan/keycertificate. -/
theorem low (domain : Domain) (cut : Cut domain) (lookup : Lookups)
 (keys : ∀ i consumer,NKR_SumLookupCertificate.Cut i consumer)
 (c : Fin 30) (t : Fin 272) (ht : t∈NJL_TagData.indices c) :
 (NKR_SumFinishData.low c).val=NJL_EndpointLookup.row (index domain t) (side t)%16 := by
 have key := (NKR_SumLookupCertificate.keys (index domain t) (side t)
  (lookup (index domain t) (side t)) (keys (index domain t) (side t))).1
 rw [coordinate domain cut lookup c t ht] at key
 have out := congrArg Prod.snd key
 exact out.trans (NKR_SumLookupCertificate.column_mod _ _)

#print axioms high
#print axioms term
#print axioms coordinate
#print axioms low
end AspisR1.NKR_SumTagAssociation
end

/- Original helper NKR_SumScratchCoordinates.lean; retained source SHA256 02105e0ac047acb61eff5bc3d515ce982d2e5b0862ba7d8391761ea2d41f8852 -/
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

/- Original helper NKR_SumCopyTail.lean; retained source SHA256 18fc86c9b9118e9a2e29b795cbc09afd7ab0a67df017a212701eee1372034d83 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyTail
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIq_Native.pool_v1.pair_forest_copy_terminal

def row (values weights : Array NQ 4#usize) : CopyRowExtension :=
 {producer_values:=Array.make 2#usize [NJB_ArrayCarrier.cell values 0,NJB_ArrayCarrier.cell values 1],
  consumer_values:=Array.make 2#usize [NJB_ArrayCarrier.cell values 2,NJB_ArrayCarrier.cell values 3],
  producer_weights:=Array.make 2#usize [NJB_ArrayCarrier.cell weights 0,NJB_ArrayCarrier.cell weights 1],
  consumer_weights:=Array.make 2#usize [NJB_ArrayCarrier.cell weights 2,NJB_ArrayCarrier.cell weights 3]}

theorem row_canonical (values weights : Array NQ 4#usize)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights) :
 FIw_ArrayValue.canonical (row values weights).producer_values ∧
 FIw_ArrayValue.canonical (row values weights).producer_weights ∧
 FIw_ArrayValue.canonical (row values weights).consumer_values ∧
 FIw_ArrayValue.canonical (row values weights).consumer_weights := by
 have cv := NJB_ArrayCarrier.canonical_cell values hv
 have cw := NJB_ArrayCarrier.canonical_cell weights hw
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cv _
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cw _
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cv _
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cw _

def reference (s : Selectors) (values weights : Array NQ 4#usize) (helper chi : NQ) :
 Result PoolV1PairForestCompiledCopyTerminalV1 := do
 let active ← Selectors.active s
 let residual ← copy_residual (row values weights) helper chi
 let scaled ← FIq_Native.field.QM31.mul active residual
 ok {residual:=scaled,active:=active}

/-- Exact218 tail after220:all8row cells,223active,215residual,and final
field product. Both returned fields and their meanings are retained;every
callee domain is proved from the caller's actual canonical arrays. -/
theorem source (s : Selectors) (values weights : Array NQ 4#usize) (helper chi : NQ)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights)
 (hhelper : Canon helper) (hchi : Canon chi) :
 ∃ active residual scaled,
 Selectors.active s=ok active ∧ Canon active ∧
 copy_residual (row values weights) helper chi=ok residual ∧ Canon residual ∧
 FIq_Native.field.QM31.mul active residual=ok scaled ∧ Canon scaled ∧
 reference s values weights helper chi=ok {residual:=scaled,active:=active} ∧
 decode residual=FIw_CopyMeaning.residual (row values weights) (decode helper) (decode chi) ∧
 decode scaled=decode active*FIw_CopyMeaning.residual (row values weights) (decode helper) (decode chi) := by
 obtain ⟨_,active,_,_,ca,_,acall⟩ := NJL_ActiveInvocation.source s hh hl
 obtain ⟨cpv,cpw,ccv,ccw⟩ := row_canonical values weights hv hw
 obtain ⟨residual,rcall,cr,vr⟩ := NJB_CopyResidual.result (row values weights) helper chi cpv ccv cpw ccw hhelper hchi
 obtain ⟨scaled,mcall,cs,vs⟩ := NJB_StubLaws.qm_mul active residual ca cr
 refine ⟨active,residual,scaled,acall,ca,rcall,cr,mcall,cs,?_,vr,?_⟩
 · simp only [reference,acall,rcall,mcall,bind_tc_ok]
 · rw [vs,vr]

#print axioms row_canonical
#print source
#print axioms source
end AspisR1.NKR_SumCopyTail
end

/- Original helper NKR_SumCopyCuts.lean; retained source SHA256 acc2a5d700cba3326f56c43b8899dd7a8596b7d80fa523e620e6ee6a87dbeed1 -/
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

/- Original helper NKR_SumCopyInvocation.lean; retained source SHA256 301e1cb25af991457addb0581192f43519d99b2eef645236abb00548e5820579 -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NKR_SumCopyCollect (Lookups)

def zero : Fin 103 → NQ := fun _=>FIq_Native.field.QM31.ZERO

def reference (lookup : Lookups) (s : Selectors) (openings : Array NQ 16#usize)
 (helper lambda chi : NQ) (append : U64) (variant : PoolV1PairForestCompiledVariantV1) :
 Result PoolV1PairForestCompiledCopyTerminalV1 := do
 let patterns ← pattern_values openings lambda
 let scratch ← NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state)
  (List.finRange 136) zero
 let (values,weights) ← NKR_SumFinishInvocation.reference (NJB_ArrayCarrier.array scratch) s patterns
 NKR_SumCopyTail.reference s values weights helper chi

/-- Full218 source invocation support. It is not yet a complete218 row:
the exact optimized tensor/legacy cohort regrouping and native parent-window
certificates remain obligations. All callee Results/domains are nevertheless
internally derived,not supplied as source-success or endpoint premises.
lookup consists only of the reviewed214 native lookup bounds. -/
theorem source (lookup : Lookups) (s : Selectors) (openings : Array NQ 16#usize)
 (helper lambda chi : NQ) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low)
 (ho : FIw_ArrayValue.canonical openings) (hhelper : Canon helper) (hlambda : Canon lambda) (hchi : Canon chi) :
 ∃ (patterns : Array NQ 14#usize) (scratch : Fin 103 → NQ)
   (values weights : Array NQ 4#usize) (active residual scaled : NQ),
 pattern_values openings lambda=ok patterns ∧
 NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state)
  (List.finRange 136) zero=ok scratch ∧
 NKR_SumCopyCollect.Trace lookup append variant s (List.finRange 136) zero scratch ∧
 NKR_SumFinishInvocation.reference (NJB_ArrayCarrier.array scratch) s patterns=ok (values,weights) ∧
 NKR_SumCopyTail.reference s values weights helper chi=ok {residual:=scaled,active:=active} ∧
 reference lookup s openings helper lambda chi append variant=ok {residual:=scaled,active:=active} ∧
 Canon active ∧ Canon residual ∧ Canon scaled ∧
 copy_residual (NKR_SumCopyTail.row values weights) helper chi=ok residual ∧
 decode scaled=decode active*FIw_CopyMeaning.residual (NKR_SumCopyTail.row values weights) (decode helper) (decode chi) := by
 obtain ⟨_,_,patterns,_,_,_,_,_,cp,patternCall⟩ := NJX_PatternRoot.source lambda openings hlambda ho
 obtain ⟨scratch,scratchCall,scratchTrace,cs⟩ := NKR_SumCopyCollect.source lookup append variant s
  (List.finRange 136) zero hh (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨dot,coefficients,finished,_,_,_,_,_,_,_,finishCall,_,_,_,cf,cw,_⟩ :=
  NKR_SumFinishInvocation.source (NJB_ArrayCarrier.array scratch) s patterns
   (NJB_ArrayCarrier.canonical_array _ cs) hh hl cp
 let values : Array NQ 4#usize := NJB_ArrayCarrier.array finished
 let weights : Array NQ 4#usize := NJB_ArrayCarrier.array dot.2
 obtain ⟨active,residual,scaled,acall,ca,rcall,cr,mcall,cm,tailCall,vr,vs⟩ :=
  NKR_SumCopyTail.source s values weights helper chi hh hl
   (NJB_ArrayCarrier.canonical_array _ cf) (NJB_ArrayCarrier.canonical_array _ cw) hhelper hchi
 refine ⟨patterns,scratch,values,weights,active,residual,scaled,patternCall,scratchCall,scratchTrace,
  finishCall,tailCall,?_,ca,cr,cm,rcall,vs⟩
 simp only [reference,patternCall,scratchCall,finishCall,tailCall,bind_tc_ok]

#print source
#print axioms source
end AspisR1.NKR_SumCopyInvocation
end
