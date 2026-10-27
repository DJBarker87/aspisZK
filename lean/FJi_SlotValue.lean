import FJi_BaseDot
import FJi_HeadCanonical
import FJi_TailTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_SlotValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FJi_Accumulations
open FIo_FieldBridge (wide)
def model (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) : AspisWideTower.WideExact :=
  FJi_BaseDot.sumTo q g slot 26+FJi_TailTrace.model q g slot

/-- Complete installed single-slot fast_dots VALUE, SAME q/g throughout. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (hg : FIo_ArrayCanon.Holds g)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=model q g slot := by
  rw [JFs_TX2_DotSuffix.body] at run
  simp only [JFs_TX2_Iterator.initial,bind_tc_ok] at run
  obtain ⟨limbs,hl,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨head,hh,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨tail,ht,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have tailValue := FJi_TailTrace.value q g slot tail hg ht
  have value := FIo_WideValues.add head tail out (FJi_HeadCanonical.value limbs head hh) tailValue.1 run
  refine ⟨value.1,?_⟩
  rw [value.2,FJi_HeadValue.value q g slot limbs head hl hh,FJi_BaseDot.model,tailValue.2]
  rfl
#print axioms value
end AspisR1.FJi_SlotValue
end
