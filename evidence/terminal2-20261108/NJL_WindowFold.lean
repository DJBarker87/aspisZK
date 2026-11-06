import NJL_WindowStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowFold
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
def run (cache : Fin 8 → NP) (o : Array NQ 16#usize) (start : Fin 9) : List (Fin 8) → NQ → Result NQ
 | [],before=>ok before
 | slot::rest,before=>do
  let middle ← NJL_WindowStep.reference (cache slot) o start slot before
  run cache o start rest middle
inductive Trace (cache : Fin 8 → NP) (o : Array NQ 16#usize) (start : Fin 9) : List (Fin 8) → NQ → NQ → Prop
 | nil (before : NQ) : Trace cache o start [] before before
 | cons {slot slots before middle after}
   (first : ∃ product,FIq_Native.field.PreparedQm31Multiplier.mul (cache slot) (NJL_WindowStep.opened o start slot)=ok product ∧
    FIq_Native.field.QM31.add before product=ok middle ∧
    NJL_WindowStep.Cut (cache slot) o start slot before product middle middle (NJB_PreparedCarrier.words (cache slot))
     (NJL_WindowStep.opened o start slot) ⟨1,before,product⟩ 2 (slot.val+1))
   (tail : Trace cache o start slots middle after) : Trace cache o start (slot::slots) before after
/-- One arbitrary-prestate native window step, then ordered finite induction.
Prepared domains are explicit generic SUPPORT and must come from actual new. -/
theorem source (theta : Fin 8 → NQ) (cache : Fin 8 → NP) (o : Array NQ 16#usize) (start : Fin 9)
 (slots : List (Fin 8)) (before : NQ) (ht : ∀ i,Canon (theta i)) (hb : Canon before)
 (ho : FIw_ArrayValue.canonical o) (domains : ∀ i,NJB_PreparedLaws.Domain (cache i) (theta i)) :
 ∃ after,run cache o start slots before=ok after ∧ Trace cache o start slots before after ∧ Canon after ∧
 decode after=decode before+(slots.map (fun i=>decode (theta i)*decode (NJL_WindowStep.opened o start i))).sum := by
 induction slots generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb,by simp⟩
 | cons slot slots ih =>
  obtain ⟨product,middle,cp,cm,call,cut,hm,vm⟩ := NJL_WindowStep.source (theta slot) before (cache slot) o start slot (ht slot) hb ho (domains slot)
  obtain ⟨after,ca,ta,ha,va⟩ := ih middle hm
  refine ⟨after,?_,.cons ⟨product,cp,cm,cut⟩ ta,ha,?_⟩
  · simp only [run,call,ca,bind_tc_ok]
  · rw [va,vm,List.map_cons,List.sum_cons];ring
#print source
#print axioms source
end AspisR1.NJL_WindowFold
end
