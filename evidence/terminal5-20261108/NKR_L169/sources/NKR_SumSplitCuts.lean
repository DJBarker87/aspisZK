import NKR_SumFinishTrace
import NKR_SumPatternTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumSplitCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NKR_SumFinishData
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
abbrev Scratch := Fin 103 → NQ
abbrev State := NKR_SumFinishBatch.State

def Domain (coordinate count : Nat) : Prop := coordinate<30 ∧ 1≤count ∧ count≤4 ∧ coordinate+count≤30

theorem batch_domain (b : Fin 9) : Domain (batchStart b) (batchCount b) := by
 have d:=NKR_SumFinishData.batch_domain b
 unfold Domain
 exact ⟨by omega,d.1,d.2.1,d.2.2.1⟩

/-- NKR_sum_tag_cell_cut:one actual from_fn callback. The native theorem
observes each payload at arbitrary coordinate/word;full typed payload equality
below aggregates ONLY those asserted projections. No readonly post-frame or
whole-array initialization/native loop is asserted. -/
def TagCell (scratch : Scratch) (s : Selectors) (coordinate count : Nat) (index : Fin 4)
 (reply out : NQ) (calls seenCoordinate : Nat) (seenHigh : Fin 64 → NQ)
 (seenLow : Fin 16 → NQ) (seenScratch : Scratch) : Prop :=
 Domain coordinate count ∧ calls=(if index.val<count then 1 else 0) ∧
 (index.val<count → seenCoordinate=coordinate+index.val ∧
  seenHigh=NJB_ArrayCarrier.cell s.high ∧ seenLow=NJB_ArrayCarrier.cell s.low ∧ seenScratch=scratch) ∧
 out=(if index.val<count then reply else FIq_Native.field.QM31.ZERO)

/-- Exact pure std reads from NKR_sum_data_cell_cut. When that optional
native target is not run,this is explicitly SOURCE/P7 bookkeeping,not native
credit. Parent array/cell association must record that classification. -/
def DataCell (scratch : Scratch) (s : Selectors) (b : Fin 9) (index : Fin 4) (weight low : NQ) : Prop :=
 Domain (batchStart b) (batchCount b) ∧
 weight=NKR_SumFinishBatch.padded (fun c=>scratch (NJL_EndpointIndices.weight c)) b index ∧
 low=NKR_SumFinishBatch.padded (fun c=>NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low c)) b index

/-- NKR_sum_arithmetic_cut:already-formed4cell arrays,2sum225/2add calls,
exact operands at every arbitrary seek,counts at both sum sites,next cursor,
and both complete4cell output frames. No103cell input/copy fact is inserted. -/
def Arithmetic (before after : State) (g : Fin 4) (coordinate count : Nat)
 (tags weights lows replies : Fin 4 → NQ) (kinds counts : Fin 4 → Nat)
 (left right : Fin 4 → Fin 4 → NQ) (calls next : Nat) : Prop :=
 Domain coordinate count ∧ calls=4 ∧ kinds=![0,1,0,1] ∧ counts 0=count ∧ counts 2=count ∧ next=coordinate+count ∧
 (∀ seek,left seek 0=tags seek ∧ right seek 0=lows seek ∧
  left seek 1=before.1 g ∧ right seek 1=replies 0 ∧
  left seek 2=weights seek ∧ right seek 2=lows seek ∧
  left seek 3=before.2 g ∧ right seek 3=replies 2) ∧
 (∀ j,after.1 j=if j=g then replies 1 else before.1 j) ∧
 (∀ j,after.2 j=if j=g then replies 3 else before.2 j)

/-- NKR_sum_pattern_product_cut:one field-product call,exact scratch/low
operands and43→26output index,reply forwarded. No coefficient state or frame
is present in this native primitive. -/
def Product (scratch : Scratch) (lows : Fin 16 → NQ) (c : Fin 43)
 (reply out left right : NQ) (output : Fin 26) (calls : Nat) : Prop :=
 calls=1 ∧ output=pOut c ∧ left=scratch (NKR_SumFinishPattern.scratchIndex c) ∧ right=lows (pLow c) ∧ out=reply

/-- NKR_sum_pattern_write_cut:one actual receiver/add/write window,old
receiver/product operands,next cursor,and full arbitrary-coordinate26cell
frame. No103scratch or product-source observation is inserted. -/
def Write (before after : Fin 26 → NQ) (c : Fin 43) (output : Fin 26)
 (product reply left right : NQ) (calls next : Nat) : Prop :=
 calls=1 ∧ next=c.val+1 ∧ left=before output ∧ right=product ∧
 ∀ j,after j=if j=output then reply else before j

/-- The frozen receiver read may move over the CLOSED pure scalar product's
empty mutable footprint. Every Result arm is preserved;success is not a
premise. This is source/P7/callee-frame bookkeeping,not a native assertion. -/
theorem pure_receiver (before : Fin 26 → NQ) (output : Fin 26) (product : Result NQ) :
 (do let receiver:=before output;let p←product;ok (receiver,p))=
 (do let p←product;let receiver:=before output;ok (receiver,p)) := by
 cases product <;> rfl

#print axioms batch_domain
#print axioms pure_receiver
end AspisR1.NKR_SumSplitCuts
end
