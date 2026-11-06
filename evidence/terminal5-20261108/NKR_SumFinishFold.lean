import NKR_SumFinishBatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishFold
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKR_SumFinishBatch

def run (tags weights lows : Fin 30 → NQ) : List (Fin 9) → State → Result State
 | [],s => ok s
 | b::bs,s => do
  let next ← step tags weights lows b s
  run tags weights lows bs next

inductive Trace (tags weights lows : Fin 30 → NQ) : List (Fin 9) → State → State → Prop
 | nil (s) : Trace tags weights lows [] s s
 | cons {b bs before next after} :
  step tags weights lows b before=ok next →
  Trace tags weights lows bs next after →
  Trace tags weights lows (b::bs) before after

/-- Finite induction for the nine source dot-batch windows. Only the native
single-window cut is required; no whole-buffer Kani loop proof is used. -/
theorem source (tags weights lows : Fin 30 → NQ) (bs : List (Fin 9)) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ after,run tags weights lows bs before=ok after ∧ Trace tags weights lows bs before after ∧
 (∀ i,Canon (after.1 i)) ∧ ∀ i,Canon (after.2 i) := by
 induction bs generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb.1,hb.2⟩
 | cons b bs ih =>
  obtain ⟨v,w,values,afterWeights,rv,rw,hv,hw',hs,hcv,hcw,hframe⟩ :=
   NKR_SumFinishBatch.source tags weights lows b before ht hw hl hb
  obtain ⟨after,rest,trace,cv,cw⟩ := ih (values,afterWeights) ⟨hcv,hcw⟩
  exact ⟨after,by simp only [run,hs,rest,bind_tc_ok],.cons hs trace,cv,cw⟩

/-- The actual four outer groups in order, each's real source partition. -/
def order : List (Fin 9) := [0,1,2,3,4,5,6,7,8]

theorem chronological : order=(List.ofFn (fun g : Fin 4=>g)).flatMap NKR_SumFinishData.batches := by decide

#print axioms source
#print axioms chronological
end AspisR1.NKR_SumFinishFold
end
