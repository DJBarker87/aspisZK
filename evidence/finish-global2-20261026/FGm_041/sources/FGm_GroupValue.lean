import FGm_ContractValue
import FIo_GroupCoefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_GroupValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode)

theorem value (f : Slice U8) (low : Array NE 16#usize) (out : NE)
    (hlow : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.s2_grouped_inactive_pair f low=ok out) :
    ∃ cs : Array NE 12#usize,
      FIo_Native.weights.s2_grouped_inactive_pair_loop0
        {start:=0#usize,«end»:=64#usize} f
        (Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok cs ∧
      FIo_ArrayCanon.Holds cs ∧ FIo_WideValues.Canon out ∧
      decode out=FGm_ContractStep.prefixSum low cs 12 := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair at run
  obtain ⟨cs,hcs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have canonical := FIo_GroupCoefficients.canonical f _ _ cs (FIo_GroupCanonical.zeros _) hcs
  have value := FGm_ContractValue.value low cs out hlow canonical run
  exact ⟨cs,hcs,canonical,value⟩

#print axioms value
end AspisR1.FGm_GroupValue
end
