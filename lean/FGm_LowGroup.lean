import FGm_GroupDispatch
import FGm_LowCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_LowGroup
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode)

theorem value (w : FIo_Native.weights.Weights) (f : Slice U8)
    (alpha0 alpha1 out : NE)
    (ha0 : FIo_WideValues.Canon alpha0) (ha1 : FIo_WideValues.Canon alpha1)
    (variant : w.variant=FIo_Native.transport.Variant.S2) (length : f.val.length=2048)
    (run : (do
      let ap0 ← FIo_Native.weights.powers 4#usize alpha0
      let ap1 ← FIo_Native.weights.powers 4#usize alpha1
      let low ← FIo_Native.weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize}
        ap0 ap1 (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)
      FIo_Native.weights.grouped_inactive_pair w f low)=ok out) :
    ∃ low : Array NE 16#usize, ∃ cs : Array NE 12#usize,
      FIo_ArrayCanon.Holds low ∧ FIo_ArrayCanon.Holds cs ∧ FIo_WideValues.Canon out ∧
      decode out=FGm_ContractStep.prefixSum low cs 12 := by
  obtain ⟨ap0,hap0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ap1,hap1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨low,hlow,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have lowCanon := FGm_LowCanonical.loop ap0 ap1
    (FIo_PowersCanonical.canonical 4#usize alpha0 ap0 ha0 hap0)
    (FIo_PowersCanonical.canonical 4#usize alpha1 ap1 ha1 hap1)
    _ _ low (FIo_GroupCanonical.zeros _) hlow
  rw [FGm_GroupDispatch.same w f low variant length] at run
  obtain ⟨cs,hcs,cc,co,value⟩ := FGm_GroupValue.value f low out lowCanon run
  exact ⟨low,cs,lowCanon,cc,co,value⟩

#print axioms value
end AspisR1.FGm_LowGroup
end
