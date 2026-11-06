import NJL_EndpointWrites
import NIH_LinkWeight
import NJB_ActiveReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_EndpointLookup
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIq_Native.pool_v1.pair_forest_copy_terminal
/-- Literal source-key registries, pinned by NJL_LOOKUP_TABLE.json; no input
endpoint or field value is invented. Native constant builder writes each
unique key once; the native cut checks its result against this scan. -/
def groupKeys : List (Nat × Nat) := [(0,0),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,12),(0,14),(1,2),(1,6),(1,10),(1,11),(1,12),(1,14),(2,0),(2,1),(2,2),(2,4),(2,5),(2,6),(2,7),(2,9),(2,10),(2,12),(2,13),(3,6),(3,7),(3,9),(3,12)]
def patternKeys : List (Nat × Nat × Nat) := [(0,0,11),(0,1,2),(0,1,6),(0,1,10),(0,1,11),(0,1,12),(0,1,14),(0,2,12),(0,4,12),(0,6,1),(0,6,12),(0,7,0),(0,7,2),(0,7,4),(0,9,6),(0,10,0),(0,11,10),(1,1,11),(1,6,12),(1,13,2),(1,13,6),(1,13,10),(1,13,14),(2,0,0),(2,1,12),(2,3,12),(2,6,6),(2,7,0),(2,7,2),(2,7,4),(2,8,7),(2,10,0),(2,11,9),(2,11,10),(2,12,1),(2,12,5),(2,12,9),(2,12,13),(3,1,12),(3,5,12),(3,6,7),(3,7,9),(3,8,6)]
def producer_row : Fin 136 → Nat := ![27,43,411,443,459,491,507,11,12,44,60,44,460,508,1008,1010,1012,1014,64,913,523,475,523,1018,539,539,555,555,571,571,587,587,603,603,619,619,635,635,651,651,667,667,683,683,699,699,715,715,731,731,747,747,763,763,779,779,795,795,811,811,827,827,843,843,59,914,914,75,918,918,91,922,922,107,926,926,123,930,930,139,934,934,155,938,938,171,942,942,187,946,946,203,950,950,219,954,954,235,958,958,251,962,962,267,966,966,283,970,970,299,974,974,315,978,978,331,982,982,347,986,986,363,990,990,379,994,994,395,998,998,875,1002,1002,891,1006,1006]
def producer_gc : Fin 136 → Nat := ![6,6,6,6,6,6,6,6,7,7,7,13,7,7,0,2,3,4,0,1,6,6,12,5,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,12,6,2,9,6,4,10,6,5,11,6,8,14,6,2,9,6,4,10,6,5,11,6,8,14,6,2,9,6,4,10,6,5,11,6,8,14,6,2,9,6,4,10,6,5,11,6,8,14,6,2,9,6,4,10,6,5,11,6,8,14,6,2,9,6,4,10,6,5,11,6,8,14]
def producer_pc : Fin 136 → Nat := ![0,0,0,0,0,0,0,4,5,7,8,18,10,10,11,12,13,14,15,9,4,4,17,16,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,17,4,1,19,4,2,20,4,3,21,4,6,22,4,1,19,4,2,20,4,3,21,4,6,22,4,1,19,4,2,20,4,3,21,4,6,22,4,1,19,4,2,20,4,3,21,4,6,22,4,1,19,4,2,20,4,3,21,4,6,22,4,1,19,4,2,20,4,3,21,4,6,22]
def consumer_row : Fin 136 → Nat := ![32,48,416,448,464,496,512,28,412,428,428,1008,1010,1012,1014,1014,1015,1015,1017,1017,1018,540,540,528,556,544,572,560,588,576,604,592,620,608,636,624,652,640,668,656,684,672,700,688,716,704,732,720,748,736,764,752,780,768,796,784,812,800,828,816,844,832,860,848,913,76,64,917,92,80,921,108,96,925,124,112,929,140,128,933,156,144,937,172,160,941,188,176,945,204,192,949,220,208,953,236,224,957,252,240,961,268,256,965,284,272,969,300,288,973,316,304,977,332,320,981,348,336,985,364,352,989,380,368,993,396,384,997,876,864,1001,892,880,1005,908,896]
def consumer_gc : Fin 136 → Nat := ![15,15,15,15,15,15,15,24,24,24,29,15,17,18,20,26,21,27,22,28,23,24,29,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,24,15,16,24,15,19,24,15,22,24,15,25,24,15,16,24,15,19,24,15,22,24,15,25,24,15,16,24,15,19,24,15,22,24,15,25,24,15,16,24,15,19,24,15,22,24,15,25,24,15,16,24,15,19,24,15,22,24,15,25,24,15,16,24,15,19,24,15,22,24,15,25,24,15]
def consumer_pc : Fin 136 → Nat := ![23,23,23,23,23,23,23,24,24,25,39,27,28,29,26,42,30,40,32,41,33,24,38,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,24,31,34,24,31,35,24,31,36,24,31,37,24,31,34,24,31,35,24,31,36,24,31,37,24,31,34,24,31,35,24,31,36,24,31,37,24,31,34,24,31,35,24,31,36,24,31,37,24,31,34,24,31,35,24,31,36,24,31,37,24,31,34,24,31,35,24,31,36,24,31,37,24,31]
def scanFrom {α : Type} [DecidableEq α] (key : α) : List α → Nat → Nat
 | [],_ => 255
 | x::xs,start => if key=x then start else scanFrom key xs (start+1)
/-- Exact source-order finite scan equation, preserving the cursor. -/
theorem scan_step {α : Type} [DecidableEq α] (key x : α) (xs : List α) (start : Nat) :
 scanFrom key (x::xs) start=if key=x then start else scanFrom key xs (start+1) := rfl
theorem group_unique : groupKeys.Nodup := by decide
theorem pattern_unique : patternKeys.Nodup := by decide
theorem size136 : (136#usize).val=136 := by scalar_tac
def link (index : Fin 136) : CompiledPoolV1PairForestLink :=
 constants.COPY_LINKS.val[index.val]'(by rw [constants.COPY_LINKS.property,size136];exact index.isLt)
def endpoint (index : Fin 136) (consumer : Bool) : CompiledPoolV1PairForestEndpoint :=
 if consumer then (link index).consumer else (link index).producer
def group (index : Fin 136) (consumer : Bool) : Nat :=
 (if consumer then 2 else 0)+(endpoint index consumer).slot.val
def row (index : Fin 136) (consumer : Bool) : Nat := (endpoint index consumer).row.val
def column (index : Fin 136) (consumer : Bool) : Nat := (row index consumer) &&& 15
def gc (index : Fin 136) (consumer : Bool) : Nat :=
 if consumer then consumer_gc index else producer_gc index
def pc (index : Fin 136) (consumer : Bool) : Nat :=
 if consumer then consumer_pc index else producer_pc index
/-- Transcription of the genuine-endpoint lookup cut's bounds. The native
observation also asserts gc/pc equal the pinned source-key scan and SAME
high-word read at row>>4; those are the definitions above and `high` below.
No final state, child Result or endpoint-equality premise is present. -/
def Cut (index : Fin 136) (consumer : Bool) : Prop :=
 row index consumer<1024 ∧ gc index consumer<30 ∧ pc index consumer<43
def groupIndex (index : Fin 136) (consumer : Bool) (cut : Cut index consumer) : Fin 30 := ⟨gc index consumer,cut.2.1⟩
def patternIndex (index : Fin 136) (consumer : Bool) (cut : Cut index consumer) : Fin 43 := ⟨pc index consumer,cut.2.2⟩
def block (index : Fin 136) (consumer : Bool) (cut : Cut index consumer) : Fin 64 :=
 ⟨row index consumer/16,by have := cut.1;omega⟩
theorem block_shift (index : Fin 136) (consumer : Bool) :
 (row index consumer) >>> 4 = row index consumer/16 := by
 rw [Nat.shiftRight_eq_div_pow]
def high (s : Selectors) (index : Fin 136) (consumer : Bool) (cut : Cut index consumer) : NQ :=
 NJB_ActiveReference.high s (block index consumer cut)
theorem member (index : Fin 136) : link index∈constants.COPY_LINKS.val := List.getElem_mem _
/-- Every actual enclosing call obtains a binary weight from the SAME link's
CLOSED complete Result, not from an independent successful-child hypothesis. -/
theorem caller_weight (index : Fin 136) (append : U64) (variant : PoolV1PairForestCompiledVariantV1) :
 ∃ weight,link_weight (link index) append variant=ok weight ∧ weight.val≤1 ∧
 (weight.val : K)=R0P.copyLinkWeight (FJk_CopyDescriptor.link (link index)) append.val (FJk_CopyDescriptor.variant variant) :=
 NIH_LinkWeight.result (link index) append variant (JGa_LinkBounds.all _ (member index))
theorem high_canonical (s : Selectors) (index : Fin 136) (consumer : Bool) (cut : Cut index consumer)
 (hs : FIw_ArrayValue.canonical s.high) : Canon (high s index consumer cut) := hs _ (List.getElem_mem _)
#print Cut
#print axioms scan_step
#print axioms group_unique
#print axioms pattern_unique
#print axioms size136
#print axioms block_shift
#print axioms member
#print axioms caller_weight
#print axioms high_canonical
end AspisR1.NJL_EndpointLookup
end
