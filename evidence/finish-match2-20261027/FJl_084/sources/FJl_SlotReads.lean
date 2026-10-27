import FJl_OuterReads
import FJl_TailReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_SlotReads
open Aeneas Aeneas.Std Result
open FJi_Accumulations
/-- All26 scalar reads and three tail reads of THIS successful slot call.
This supplies provenance that backend VALUE theorems intentionally abstracted. -/
theorem reached (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    (∀ n,n<26 → FJl_InnerReads.Read q slot n) ∧
      ∃ q0 q1 q2 : FIo_FieldBridge.NQ,
        FJi_TailInputs.read0 q slot=ok q0 ∧ FJi_TailInputs.read1 q slot=ok q1 ∧
        FJi_TailInputs.read2 q slot=ok q2 := by
  rw [JFs_TX2_DotSuffix.body] at run
  simp only [JFs_TX2_Iterator.initial,bind_tc_ok] at run
  obtain ⟨limbs,hl,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨head,hh,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tail,ht,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨FJl_OuterReads.value q g slot limbs hl,FJl_TailReads.reached q g slot tail ht⟩
#print axioms reached
end AspisR1.FJl_SlotReads
end
