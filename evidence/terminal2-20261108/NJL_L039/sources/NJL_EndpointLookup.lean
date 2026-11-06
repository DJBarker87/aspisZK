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
 scanFrom (group index consumer,column index consumer) groupKeys 0
def pc (index : Fin 136) (consumer : Bool) : Nat :=
 scanFrom (group index consumer,(endpoint index consumer).pattern.val,column index consumer) patternKeys 0
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
