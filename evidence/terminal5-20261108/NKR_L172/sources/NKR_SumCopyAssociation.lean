import NKR_SumCopyAlgebraCombined
import NKR_SumFinishCohort
import RPv_FJk_CopyFullFold
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyAssociation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NKR_SumCopyCollect (Lookups State)
abbrev Keys := ∀ i consumer,NKR_SumLookupCertificate.Cut i consumer

def link (i : Fin 136) : R0P.CopyLink := FJk_CopyDescriptor.link (NJL_EndpointLookup.link i)
def endpoint (i : Fin 136) (consumer : Bool) : R0P.CopyEndpoint := NKR_SumLegacyRows.endpoint (link i) consumer

def gi (lookup : Lookups) (i : Fin 136) (consumer : Bool) : Fin 30 := NJL_EndpointLookup.groupIndex i consumer (lookup i consumer)
def pi (lookup : Lookups) (i : Fin 136) (consumer : Bool) : Fin 43 := NJL_EndpointLookup.patternIndex i consumer (lookup i consumer)
def high (lookup : Lookups) (s : Selectors) (i : Fin 136) (consumer : Bool) : K := decode (NJL_EndpointLookup.high s i consumer (lookup i consumer))
def low (s : Selectors) (c : Fin 30) : K := decode (NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low c))
def plow (s : Selectors) (c : Fin 43) : K := decode (NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.pLow c))

theorem bounds (i : Fin 136) (consumer : Bool) :
 (NJL_EndpointLookup.endpoint i consumer).row.val<1024 ∧
 (NJL_EndpointLookup.endpoint i consumer).slot.val<2 ∧
 (NJL_EndpointLookup.endpoint i consumer).pattern.val<14 := by
 have h:=JGa_LinkBounds.all _ (NJL_EndpointLookup.member i)
 cases consumer
 · exact ⟨h.1.1,h.1.2.1,h.1.2.2⟩
 · exact ⟨h.2.1.1,h.2.1.2.1,h.2.1.2.2⟩

theorem descriptor_row (i : Fin 136) (consumer : Bool) :
 (endpoint i consumer).row.val=NJL_EndpointLookup.row i consumer := by
 have h:=(bounds i consumer).1
 cases consumer <;> exact Nat.mod_eq_of_lt h

theorem descriptor_slot (i : Fin 136) (consumer : Bool) :
 (endpoint i consumer).slot.val=(NJL_EndpointLookup.endpoint i consumer).slot.val := by
 have h:=(bounds i consumer).2.1
 cases consumer <;> exact Nat.mod_eq_of_lt h

theorem descriptor_pattern (i : Fin 136) (consumer : Bool) :
 (endpoint i consumer).pattern.val=(NJL_EndpointLookup.endpoint i consumer).pattern.val := by
 have h:=(bounds i consumer).2.2
 cases consumer <;> exact Nat.mod_eq_of_lt h

theorem group_key (lookup : Lookups) (keys : Keys) (i : Fin 136) (consumer : Bool) :
 NKR_SumFinishData.group (gi lookup i consumer)=NKR_SumLegacyRows.group consumer (endpoint i consumer) := by
 have key:=(NKR_SumLookupCertificate.keys i consumer (lookup i consumer) (keys i consumer)).1
 have v:=congrArg Prod.fst key
 apply Fin.ext
 change (NKR_SumFinishData.group (gi lookup i consumer)).val=(endpoint i consumer).slot.val+(if consumer then 2 else 0)
 rw [descriptor_slot]
 change (NKR_SumFinishData.group (gi lookup i consumer)).val=
  (NJL_EndpointLookup.endpoint i consumer).slot.val+(if consumer then 2 else 0)
 exact v.trans (Nat.add_comm _ _)

theorem low_key (lookup : Lookups) (keys : Keys) (i : Fin 136) (consumer : Bool) :
 (NKR_SumFinishData.low (gi lookup i consumer)).val=NJL_EndpointLookup.row i consumer%16 := by
 have key:=(NKR_SumLookupCertificate.keys i consumer (lookup i consumer) (keys i consumer)).1
 exact (congrArg Prod.snd key).trans (NKR_SumLookupCertificate.column_mod i consumer)

theorem pattern_group_key (lookup : Lookups) (keys : Keys) (i : Fin 136) (consumer : Bool) :
 NKR_SumLookupCertificate.patternGroup (pi lookup i consumer)=NKR_SumFinishData.group (gi lookup i consumer) := by
 have key:=NKR_SumLookupCertificate.keys i consumer (lookup i consumer) (keys i consumer)
 apply Fin.ext
 exact (congrArg (fun k=>k.1.1) key.2).trans (congrArg Prod.fst key.1).symm

theorem pattern_key (lookup : Lookups) (keys : Keys) (i : Fin 136) (consumer : Bool) :
 NJB_PatternReference.pattern (NKR_SumFinishData.pOut (pi lookup i consumer))=(endpoint i consumer).pattern := by
 have key:=(NKR_SumLookupCertificate.keys i consumer (lookup i consumer) (keys i consumer)).2
 apply Fin.ext
 exact (congrArg (fun k=>k.1.2) key).trans (descriptor_pattern i consumer).symm

theorem pattern_low_key (lookup : Lookups) (keys : Keys) (s : Selectors) (i : Fin 136) (consumer : Bool) :
 plow s (pi lookup i consumer)=low s (gi lookup i consumer) := by
 have key:=NKR_SumLookupCertificate.keys i consumer (lookup i consumer) (keys i consumer)
 have eq : NKR_SumFinishData.pLow (pi lookup i consumer)=NKR_SumFinishData.low (gi lookup i consumer) :=
  Fin.ext ((congrArg Prod.snd key.2).trans (congrArg Prod.snd key.1).symm)
 exact congrArg (fun c=>decode (NJB_ArrayCarrier.cell s.low c)) eq

theorem selector (lookup : Lookups) (keys : Keys) (s : Selectors) (i : Fin 136) (consumer : Bool) :
 high lookup s i consumer*low s (gi lookup i consumer)=
 R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i consumer).row := by
 have hr : decode (NJL_EndpointLookup.high s i consumer (lookup i consumer))=
  FIv_NativeArray.value s.high (NJL_EndpointLookup.row i consumer/16) :=
  NJB_ActiveAssociation.high_same s (NJL_EndpointLookup.block i consumer (lookup i consumer))
 have lr : decode (NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low (gi lookup i consumer)))=
  FIv_NativeArray.value s.low (NKR_SumFinishData.low (gi lookup i consumer)).val :=
  NJB_ActiveAssociation.low_same s _
 change decode (NJL_EndpointLookup.high s i consumer (lookup i consumer))*
  decode (NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low (gi lookup i consumer)))=
  FIv_NativeArray.value s.high ((endpoint i consumer).row.val/16)*
   FIv_NativeArray.value s.low ((endpoint i consumer).row.val%16)
 rw [hr,lr,descriptor_row,low_key lookup keys]
 rfl

theorem sum_finRange {n : Nat} (f : Fin n → K) : ((List.finRange n).map f).sum=∑ i,f i := by
 change ((List.ofFn (fun i : Fin n=>i)).map f).sum=_
 simp only [List.map_ofFn,List.sum_ofFn]

theorem sum_filter {A : Type} (xs : List A) (p : A → Bool) (f : A → K) :
 ((xs.filter p).map f).sum=(xs.map (fun x=>if p x then f x else 0)).sum := by
 induction xs with
 | nil => rfl
 | cons x xs ih => cases h : p x <;> simp [h,ih]

theorem native_list : List.ofFn NJL_EndpointLookup.link=constants.COPY_LINKS.val := by
 apply List.ext_getElem
 · simp only [List.length_ofFn,constants.COPY_LINKS.property,NJL_EndpointLookup.size136]
 · intro i hi hj
   simp only [List.getElem_ofFn,NJL_EndpointLookup.link]

theorem link_sum (f : R0P.CopyLink → K) : (R0P.copyLinks.map f).sum=∑ i : Fin 136,f (link i) := by
 rw [←FJk_CopyRegistry.value,List.map_map,←native_list,List.map_ofFn,List.sum_ofFn]
 rfl

def canonicalIndex (t : Fin 272) : Fin 136 := ⟨t.val%136,Nat.mod_lt _ (by decide)⟩
def canonicalSide (t : Fin 272) : Bool := decide (136≤t.val)
def pairEncode (p : Fin 136 × Bool) : Fin 272 :=
 ⟨p.1.val+(if p.2 then 136 else 0),by have:=p.1.isLt;split <;>omega⟩
def pairDecode (t : Fin 272) : Fin 136 × Bool := (canonicalIndex t,canonicalSide t)

theorem pair_left (p : Fin 136 × Bool) : pairDecode (pairEncode p)=p := by
 rcases p with ⟨i,b⟩
 cases b <;> apply Prod.ext
 · apply Fin.ext
   simp only [pairDecode,pairEncode,canonicalIndex,Bool.false_eq_true,if_false,Nat.add_zero]
   have:=i.isLt
   omega
 · simp only [pairDecode,pairEncode,canonicalSide,Bool.false_eq_true,if_false,Nat.add_zero]
   have:=i.isLt
   simp only [decide_eq_false_iff_not]
   omega
 · apply Fin.ext
   simp only [pairDecode,pairEncode,canonicalIndex,if_true]
   have:=i.isLt
   omega
 · simp only [pairDecode,pairEncode,canonicalSide,if_true]
   simp only [decide_eq_true_eq]
   omega

theorem pair_right (t : Fin 272) : pairEncode (pairDecode t)=t := by
 apply Fin.ext
 change t.val%136+(if decide (136≤t.val) then 136 else 0)=t.val
 have:=t.isLt
 simp only [decide_eq_true_eq]
 split_ifs <;> omega

theorem canonical_encoded (domain : NKR_SumTagPermutation.Domain) (t : Fin 272) :
 pairDecode (NKR_SumTagPermutation.encoded domain t)=(NKR_SumTagPermutation.index domain t,NKR_SumTagPermutation.side t) := by
 exact pair_left (NKR_SumTagPermutation.index domain t,NKR_SumTagPermutation.side t)

theorem sum_pairs (f : Fin 136 → Bool → K) :
 (∑ t : Fin 272,f (canonicalIndex t) (canonicalSide t))=∑ i : Fin 136,(f i false+f i true) := by
 calc
  _=∑ p : Fin 136 × Bool,f p.1 p.2 := by
   refine Finset.sum_bij (fun t _=>pairDecode t) ?_ ?_ ?_ ?_
   · intro t ht
     exact Finset.mem_univ _
   · intro t ht u hu h
     exact (pair_right t).symm.trans ((congrArg pairEncode h).trans (pair_right u))
   · intro p hp
     exact ⟨pairEncode p,Finset.mem_univ _,pair_left p⟩
   · intro t ht
     rfl
  _=_ := by
   rw [Fintype.sum_prod_type]
   apply Finset.sum_congr rfl
   intro i hi
   simp

/-- Arbitrary caller field expression is transported from the sorted272tag
positions to136genuine producer/consumer entries by the native metadata
injection and finite bijection,not by concrete table normalization. -/
theorem tag_transport (domain : NKR_SumTagPermutation.Domain) (permutation : NKR_SumTagPermutation.Cut)
 (f : Fin 136 → Bool → K) :
 (∑ t : Fin 272,f (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))=
 ∑ i : Fin 136,(f i false+f i true) := by
 have tr:=NKR_SumTagPermutation.sum_transport domain permutation
  (fun t=>f (canonicalIndex t) (canonicalSide t))
 rw [sum_finRange,sum_finRange] at tr
 have left : (fun t : Fin 272=>f (canonicalIndex (NKR_SumTagPermutation.encoded domain t))
  (canonicalSide (NKR_SumTagPermutation.encoded domain t)))=
  (fun t=>f (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)) := by
  funext t
  have h:=canonical_encoded domain t
  exact congrArg (fun p : Fin 136 × Bool=>f p.1 p.2) h
 rw [left] at tr
 exact tr.trans (sum_pairs f)

theorem list_sum_mul {A : Type} (xs : List A) (f : A → K) (x : K) :
 (xs.map f).sum*x=(xs.map (fun a=>f a*x)).sum := by
 induction xs with
 | nil => simp
 | cons a xs ih => simp only [List.map_cons,List.sum_cons,add_mul,ih]

def tagTerm (lookup : Lookups) (s : Selectors) (g : Fin 4) (i : Fin 136) (consumer : Bool) : K :=
 if NKR_SumLegacyRows.group consumer (endpoint i consumer)=g then
  high lookup s i consumer*low s (gi lookup i consumer)*((link i).tag : K) else 0

theorem tag_bucket (lookup : Lookups) (keys : Keys) (domain : NKR_SumTagPermutation.Domain)
 (metadata : NKR_SumTagAssociation.Cut domain) (s : Selectors) (g : Fin 4) (c : Fin 30) :
 (if NKR_SumFinishData.group c=g then NKR_SumFinishCohort.tag s c*low s c else 0)=
 ((NJL_TagData.indices c).map (fun t=>tagTerm lookup s g
  (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))).sum := by
 by_cases same : NKR_SumFinishData.group c=g
 · simp only [if_pos same]
   change ((NJL_TagData.indices c).map (fun t=>decode (NJB_ActiveReference.high s (NJL_TagData.block t))*(NJL_TagData.tag t).val)).sum*low s c=_
   rw [list_sum_mul]
   apply congrArg List.sum
   apply List.map_congr_left
   intro t ht
   have cg:=NKR_SumTagAssociation.coordinate domain metadata lookup c t ht
   change gi lookup (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)=c at cg
   have gg : NKR_SumLegacyRows.group (NKR_SumTagPermutation.side t)
     (endpoint (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))=g := by
    rw [←group_key lookup keys,show gi lookup (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)=c from cg]
    exact same
   rw [NKR_SumTagAssociation.term domain metadata lookup s t]
   simp only [tagTerm,if_pos gg]
   change (high lookup s _ _*((link _).tag : K))*low s c=
    high lookup s _ _*low s (gi lookup _ _)*((link _).tag : K)
   rw [cg]
   ring
 · simp only [if_neg same]
   have zero : ((NJL_TagData.indices c).map (fun t=>tagTerm lookup s g
    (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)))=
    (NJL_TagData.indices c).map (fun _=>0) := by
    apply List.map_congr_left
    intro t ht
    have cg:=NKR_SumTagAssociation.coordinate domain metadata lookup c t ht
    change gi lookup (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)=c at cg
    have gg : NKR_SumLegacyRows.group (NKR_SumTagPermutation.side t)
      (endpoint (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))≠g := by
     rw [←group_key lookup keys,show gi lookup (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)=c from cg]
     exact same
    exact if_neg gg
   rw [zero]
   simp

theorem tag_value (lookup : Lookups) (keys : Keys) (domain : NKR_SumTagPermutation.Domain)
 (permutation : NKR_SumTagPermutation.Cut) (metadata : NKR_SumTagAssociation.Cut domain)
 (s : Selectors) (g : Fin 4) :
 NKR_SumFinishCohort.baseValues s g=∑ i : Fin 136,(tagTerm lookup s g i false+tagTerm lookup s g i true) := by
 calc
  _=((List.finRange 30).map (fun c=>((NJL_TagData.indices c).map (fun t=>tagTerm lookup s g
   (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))).sum)).sum := by
   apply congrArg List.sum
   apply List.map_congr_left
   intro c hc
   exact tag_bucket lookup keys domain metadata s g c
  _=(((List.finRange 30).flatMap NJL_TagData.indices).map (fun t=>tagTerm lookup s g
   (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t))).sum :=
   (NKR_SumFinishExpanded.sum_flatMap NJL_TagData.indices
    (fun t=>tagTerm lookup s g (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t)) (List.finRange 30)).symm
  _=∑ t : Fin 272,tagTerm lookup s g (NKR_SumTagPermutation.index domain t) (NKR_SumTagPermutation.side t) := by
   rw [NKR_SumTagPartition.source,sum_finRange]
  _=_ := tag_transport domain permutation (tagTerm lookup s g)

def patternTerm (s : Selectors) (terms : Array NQ 14#usize) (c : Fin 43) : K :=
 decode (NJB_ArrayCarrier.cell terms (NJB_PatternReference.pattern (NKR_SumFinishData.pOut c)))*plow s c

theorem dot_finite (terms : Fin 14 → K) (coefficients : Fin 26 → K) (g : Fin 4) :
 NJL_PatternMeaning.dot terms coefficients g=
 ∑ p : Fin 26,if p∈NJB_PatternReference.coordinates g then terms (NJB_PatternReference.pattern p)*coefficients p else 0 := by
 unfold NJL_PatternMeaning.dot NJB_PatternReference.coordinates
 rw [sum_filter]
 simp only [List.map_ofFn,List.sum_ofFn]
 apply Finset.sum_congr rfl
 intro p hp
 have member : p∈NJB_PatternReference.coordinates g ↔
  NJB_PatternReference.offset g.castSucc≤p.val ∧ p.val<NJB_PatternReference.offset g.succ := by
  simp [NJB_PatternReference.coordinates]
 simp [member]

theorem coefficient_finite (scratch : State) (s : Selectors) (p : Fin 26) :
 NKR_SumFinishCohort.coefficient (NJB_ArrayCarrier.array scratch) s p=
 ∑ c : Fin 43,if NKR_SumFinishData.pOut c=p then
 decode (scratch (NJL_EndpointIndices.pattern c))*plow s c else 0 := by
 unfold NKR_SumFinishCohort.coefficient
 rw [sum_finRange]
 apply Finset.sum_congr rfl
 intro c hc
 rw [NJB_ArrayCarrier.cell_array]
 rfl

/-- The26pattern outputs contract exactly the actual43coefficient cells.
This is the key sparse-basis step from220's cohort to endpoint coordinates. -/
theorem pattern_value (scratch : State) (s : Selectors) (terms : Array NQ 14#usize) (g : Fin 4) :
 NJL_PatternMeaning.dot (fun i=>decode (NJB_ArrayCarrier.cell terms i))
  (NKR_SumFinishCohort.coefficient (NJB_ArrayCarrier.array scratch) s) g=
 ∑ c : Fin 43,if NKR_SumLookupCertificate.patternGroup c=g then
 patternTerm s terms c*decode (scratch (NJL_EndpointIndices.pattern c)) else 0 := by
 rw [dot_finite]
 simp_rw [coefficient_finite]
 rw [NKR_SumRegroup.contraction]
 apply Finset.sum_congr rfl
 intro c hc
 rw [NKR_SumRegroup.bucket_iff]
 by_cases h : NKR_SumLookupCertificate.patternGroup c=g
 · simp only [if_pos h]
   unfold patternTerm
   ring
 · simp only [if_neg h]

def weightSum (lookup : Lookups) (s : Selectors) (append : U64) (variant : PoolV1PairForestCompiledVariantV1) (c : Fin 30) : K :=
 ∑ i : Fin 136,((if gi lookup i false=c then high lookup s i false*NKR_SumCollectMeaning.weight i append variant else 0)+
  (if gi lookup i true=c then high lookup s i true*NKR_SumCollectMeaning.weight i append variant else 0))
def patternSum (lookup : Lookups) (s : Selectors) (c : Fin 43) : K :=
 ∑ i : Fin 136,((if pi lookup i false=c then high lookup s i false else 0)+
  (if pi lookup i true=c then high lookup s i true else 0))

def weightTerm (s : Selectors) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (i : Fin 136) (consumer : Bool) : K :=
 NKR_SumLegacyRows.weightTerm (FIw_CopyEndpoint.modelSelectors s) append.val (FJk_CopyDescriptor.variant variant) (link i) consumer

def patternEndpoint (s : Selectors) (terms : Array NQ 14#usize) (i : Fin 136) (consumer : Bool) : K :=
 R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i consumer).row*
  decode (NJB_ArrayCarrier.cell terms (endpoint i consumer).pattern)

theorem weight_regroup (lookup : Lookups) (keys : Keys) (s : Selectors) (scratch : State)
 (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (coordinates : ∀ c,decode (scratch (NJL_EndpointIndices.weight c))=weightSum lookup s append variant c) (g : Fin 4) :
 NKR_SumFinishCohort.baseWeights (NJB_ArrayCarrier.array scratch) s g=
 ∑ i : Fin 136,((if NKR_SumLegacyRows.group false (endpoint i false)=g then weightTerm s append variant i false else 0)+
  (if NKR_SumLegacyRows.group true (endpoint i true)=g then weightTerm s append variant i true else 0)) := by
 have one (i : Fin 136) (b : Bool) :
  (if NKR_SumFinishData.group (gi lookup i b)=g then
   low s (gi lookup i b)*(high lookup s i b*NKR_SumCollectMeaning.weight i append variant) else 0)=
  (if NKR_SumLegacyRows.group b (endpoint i b)=g then weightTerm s append variant i b else 0) := by
   rw [group_key lookup keys]
   by_cases h : NKR_SumLegacyRows.group b (endpoint i b)=g
   · simp only [if_pos h]
     change low s (gi lookup i b)*(high lookup s i b*NKR_SumCollectMeaning.weight i append variant)=
      R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i b).row*NKR_SumCollectMeaning.weight i append variant
     rw [←selector lookup keys]
     ring
   · simp only [if_neg h]
 calc
  _=(∑ c : Fin 30,if NKR_SumFinishData.group c=g then low s c*weightSum lookup s append variant c else 0) := by
   unfold NKR_SumFinishCohort.baseWeights
   rw [sum_finRange]
   apply Finset.sum_congr rfl
   intro c hc
   change (if NKR_SumFinishData.group c=g then decode (scratch (NJL_EndpointIndices.weight c))*low s c else 0)=_
   rw [coordinates]
   split_ifs <;> ring
  _=(∑ i : Fin 136,((if NKR_SumFinishData.group (gi lookup i false)=g then
    low s (gi lookup i false)*(high lookup s i false*NKR_SumCollectMeaning.weight i append variant) else 0)+
   (if NKR_SumFinishData.group (gi lookup i true)=g then
    low s (gi lookup i true)*(high lookup s i true*NKR_SumCollectMeaning.weight i append variant) else 0))) :=
    NKR_SumTensorAlgebra.contraction_two (gi lookup · false) (gi lookup · true)
     (fun c=>NKR_SumFinishData.group c=g) (low s)
     (fun i=>high lookup s i false*NKR_SumCollectMeaning.weight i append variant)
     (fun i=>high lookup s i true*NKR_SumCollectMeaning.weight i append variant)
  _=_ := by simp_rw [one]

theorem pattern_regroup (lookup : Lookups) (keys : Keys) (s : Selectors) (scratch : State)
 (terms : Array NQ 14#usize)
 (coordinates : ∀ c,decode (scratch (NJL_EndpointIndices.pattern c))=patternSum lookup s c) (g : Fin 4) :
 NJL_PatternMeaning.dot (fun i=>decode (NJB_ArrayCarrier.cell terms i))
  (NKR_SumFinishCohort.coefficient (NJB_ArrayCarrier.array scratch) s) g=
 ∑ i : Fin 136,((if NKR_SumLegacyRows.group false (endpoint i false)=g then patternEndpoint s terms i false else 0)+
  (if NKR_SumLegacyRows.group true (endpoint i true)=g then patternEndpoint s terms i true else 0)) := by
 have one (i : Fin 136) (b : Bool) :
  (if NKR_SumLookupCertificate.patternGroup (pi lookup i b)=g then patternTerm s terms (pi lookup i b)*high lookup s i b else 0)=
  (if NKR_SumLegacyRows.group b (endpoint i b)=g then patternEndpoint s terms i b else 0) := by
   rw [pattern_group_key lookup keys,group_key lookup keys]
   by_cases h : NKR_SumLegacyRows.group b (endpoint i b)=g
   · simp only [if_pos h]
     unfold patternTerm
     rw [pattern_key lookup keys,pattern_low_key lookup keys]
     unfold patternEndpoint
     rw [←selector lookup keys]
     ring
   · simp only [if_neg h]
 rw [pattern_value]
 simp_rw [coordinates]
 calc
  _=(∑ i : Fin 136,((if NKR_SumLookupCertificate.patternGroup (pi lookup i false)=g then
    patternTerm s terms (pi lookup i false)*high lookup s i false else 0)+
   (if NKR_SumLookupCertificate.patternGroup (pi lookup i true)=g then
    patternTerm s terms (pi lookup i true)*high lookup s i true else 0))) :=
    NKR_SumTensorAlgebra.contraction_two (pi lookup · false) (pi lookup · true)
     (fun c=>NKR_SumLookupCertificate.patternGroup c=g) (patternTerm s terms)
     (high lookup s · false) (high lookup s · true)
  _=_ := by simp_rw [one]

def valueTerm (s : Selectors) (terms : Array NQ 14#usize) (i : Fin 136) (consumer : Bool) : K :=
 NKR_SumLegacyRows.valueTerm (FIw_CopyEndpoint.modelSelectors s) (FIw_ArrayValue.decoded terms) (link i) consumer

theorem tag_pattern (lookup : Lookups) (keys : Keys) (s : Selectors) (terms : Array NQ 14#usize)
 (g : Fin 4) (i : Fin 136) (consumer : Bool) :
 tagTerm lookup s g i consumer+
 (if NKR_SumLegacyRows.group consumer (endpoint i consumer)=g then patternEndpoint s terms i consumer else 0)=
 if NKR_SumLegacyRows.group consumer (endpoint i consumer)=g then valueTerm s terms i consumer else 0 := by
 by_cases h : NKR_SumLegacyRows.group consumer (endpoint i consumer)=g
 · simp only [tagTerm,if_pos h]
   rw [selector lookup keys]
   change R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i consumer).row*((link i).tag : K)+
     R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i consumer).row*decode (NJB_ArrayCarrier.cell terms (endpoint i consumer).pattern)=
    R0P.copySelectorRow (FIw_CopyEndpoint.modelSelectors s) (endpoint i consumer).row*
      (((link i).tag : K)+decode (NJB_ArrayCarrier.cell terms (endpoint i consumer).pattern))
   ring
 · simp only [tagTerm,if_neg h,zero_add]

theorem legacy_values (s : Selectors) (terms : Array NQ 14#usize) (append : U64)
 (variant : PoolV1PairForestCompiledVariantV1) (g : Fin 4) :
 NKR_SumLegacyRows.values (FJk_CopyFullFold.model s terms append variant) g=
 ∑ i : Fin 136,((if NKR_SumLegacyRows.group false (endpoint i false)=g then valueTerm s terms i false else 0)+
  (if NKR_SumLegacyRows.group true (endpoint i true)=g then valueTerm s terms i true else 0)) := by
 have v:=NKR_SumLegacyRows.fold_values (FIw_CopyEndpoint.modelSelectors s) (FIw_ArrayValue.decoded terms)
  append.val (FJk_CopyDescriptor.variant variant) FJk_CopyFullFold.initial R0P.copyLinks g
 have z : NKR_SumLegacyRows.values FJk_CopyFullFold.initial g=0 := by
  unfold NKR_SumLegacyRows.values FJk_CopyFullFold.initial
  split <;> rfl
 rw [z,zero_add,link_sum] at v
 simpa only [FJk_CopyFullFold.model,valueTerm,endpoint,link,NKR_SumLegacyRows.endpoint,eq_comm] using v

theorem legacy_weights (s : Selectors) (terms : Array NQ 14#usize) (append : U64)
 (variant : PoolV1PairForestCompiledVariantV1) (g : Fin 4) :
 NKR_SumLegacyRows.weights (FJk_CopyFullFold.model s terms append variant) g=
 ∑ i : Fin 136,((if NKR_SumLegacyRows.group false (endpoint i false)=g then weightTerm s append variant i false else 0)+
  (if NKR_SumLegacyRows.group true (endpoint i true)=g then weightTerm s append variant i true else 0)) := by
 have v:=NKR_SumLegacyRows.fold_weights (FIw_CopyEndpoint.modelSelectors s) (FIw_ArrayValue.decoded terms)
  append.val (FJk_CopyDescriptor.variant variant) FJk_CopyFullFold.initial R0P.copyLinks g
 have z : NKR_SumLegacyRows.weights FJk_CopyFullFold.initial g=0 := by
  unfold NKR_SumLegacyRows.weights FJk_CopyFullFold.initial
  split <;> rfl
 rw [z,zero_add,link_sum] at v
 simpa only [FJk_CopyFullFold.model,weightTerm,endpoint,link,NKR_SumLegacyRows.endpoint,eq_comm] using v

/-- Algebraic join only:the two coordinate premises are internally derived
by `source` below from the complete actual136link computation. They are not
positive-row-root hypotheses or independent endpoint equalities. -/
theorem rows (lookup : Lookups) (keys : Keys) (domain : NKR_SumTagPermutation.Domain)
 (permutation : NKR_SumTagPermutation.Cut) (metadata : NKR_SumTagAssociation.Cut domain)
 (s : Selectors) (scratch : State) (terms : Array NQ 14#usize) (append : U64)
 (variant : PoolV1PairForestCompiledVariantV1)
 (hw : ∀ c,decode (scratch (NJL_EndpointIndices.weight c))=weightSum lookup s append variant c)
 (hp : ∀ c,decode (scratch (NJL_EndpointIndices.pattern c))=patternSum lookup s c) :
 (∀ g,NKR_SumFinishCohort.values (NJB_ArrayCarrier.array scratch) s terms g=
  NKR_SumLegacyRows.values (FJk_CopyFullFold.model s terms append variant) g) ∧
 (∀ g,NKR_SumFinishCohort.baseWeights (NJB_ArrayCarrier.array scratch) s g=
  NKR_SumLegacyRows.weights (FJk_CopyFullFold.model s terms append variant) g) := by
 constructor
 · intro g
   unfold NKR_SumFinishCohort.values
   rw [tag_value lookup keys domain permutation metadata,pattern_regroup lookup keys s scratch terms hp,
    legacy_values,←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro i hi
   calc
    _=(tagTerm lookup s g i false+
       (if NKR_SumLegacyRows.group false (endpoint i false)=g then patternEndpoint s terms i false else 0))+
      (tagTerm lookup s g i true+
       (if NKR_SumLegacyRows.group true (endpoint i true)=g then patternEndpoint s terms i true else 0)) := by ring
    _=_ := by rw [tag_pattern lookup keys,tag_pattern lookup keys]
 · intro g
   exact (weight_regroup lookup keys s scratch append variant hw g).trans (legacy_weights s terms append variant g).symm

/-- Complete eight-channel218 tensor/legacy association. The SAME scratch
is constructed from all136actual217/214calls;220is consumed at that exact
scratch/selectors/patterns. Every field/callee/domain/output clause is derived.
Root premises are canonical actual inputs and the reviewed native metadata
cuts only;there is no source-success or desired-output/cohort premise. -/
theorem source (lookup : Lookups) (keys : Keys) (domain : NKR_SumTagPermutation.Domain)
 (permutation : NKR_SumTagPermutation.Cut) (metadata : NKR_SumTagAssociation.Cut domain)
 (s : Selectors) (terms : Array NQ 14#usize) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) (ht : FIw_ArrayValue.canonical terms) :
 ∃ (scratch : State) (outValues outWeights : Array NQ 4#usize),
 NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state)
  (List.finRange 136) NKR_SumCopyInvocation.zero=ok scratch ∧
 NKR_SumFinishInvocation.reference (NJB_ArrayCarrier.array scratch) s terms=ok (outValues,outWeights) ∧
 FIw_ArrayValue.canonical outValues ∧ FIw_ArrayValue.canonical outWeights ∧
 (∀ g,decode (NJB_ArrayCarrier.cell outValues g)=NKR_SumLegacyRows.values (FJk_CopyFullFold.model s terms append variant) g) ∧
 (∀ g,decode (NJB_ArrayCarrier.cell outWeights g)=NKR_SumLegacyRows.weights (FJk_CopyFullFold.model s terms append variant) g) := by
 obtain ⟨scratch,call,cs,weightCoordinates,patternCoordinates⟩ := NKR_SumScratchCoordinates.source
  lookup append variant s (List.finRange 136) NKR_SumCopyInvocation.zero hh (fun _=>FIv_NativeValue.zero.1)
 have hw (c : Fin 30) : decode (scratch (NJL_EndpointIndices.weight c))=weightSum lookup s append variant c := by
  have h:=weightCoordinates c
  change decode (scratch (NJL_EndpointIndices.weight c))=decode FIq_Native.field.QM31.ZERO+_ at h
  rw [FIv_NativeValue.zero.2,zero_add,sum_finRange] at h
  simpa only [weightSum,gi,high,eq_comm] using h
 have hp (c : Fin 43) : decode (scratch (NJL_EndpointIndices.pattern c))=patternSum lookup s c := by
  have h:=patternCoordinates c
  change decode (scratch (NJL_EndpointIndices.pattern c))=decode FIq_Native.field.QM31.ZERO+_ at h
  rw [FIv_NativeValue.zero.2,zero_add,sum_finRange] at h
  simpa only [patternSum,pi,high,eq_comm] using h
 obtain ⟨values,weights,finishCall,cv,cw,vv,vw⟩ := NKR_SumFinishCohort.source (NJB_ArrayCarrier.array scratch) s terms
  (NJB_ArrayCarrier.canonical_array _ cs) hh hl ht
 have eq:=rows lookup keys domain permutation metadata s scratch terms append variant hw hp
 exact ⟨scratch,values,weights,call,finishCall,cv,cw,fun g=>(vv g).trans (eq.1 g),fun g=>(vw g).trans (eq.2 g)⟩

#print axioms bounds
#print axioms descriptor_row
#print axioms descriptor_slot
#print axioms descriptor_pattern
#print axioms group_key
#print axioms low_key
#print axioms pattern_group_key
#print axioms pattern_key
#print axioms pattern_low_key
#print axioms selector
#print axioms sum_finRange
#print axioms sum_filter
#print axioms native_list
#print axioms link_sum
#print axioms pair_left
#print axioms pair_right
#print axioms canonical_encoded
#print axioms sum_pairs
#print axioms tag_transport
#print axioms list_sum_mul
#print axioms tag_bucket
#print axioms tag_value
#print axioms dot_finite
#print axioms coefficient_finite
#print axioms pattern_value
#print axioms weight_regroup
#print axioms pattern_regroup
#print axioms tag_pattern
#print axioms legacy_values
#print axioms legacy_weights
#print axioms rows
#print source
#print axioms source
end AspisR1.NKR_SumCopyAssociation
end
