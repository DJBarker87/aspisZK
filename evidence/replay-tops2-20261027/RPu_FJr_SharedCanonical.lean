import RPu_FJr_NativeRow
import RPu_FJg_SharedHighTrace
import RPu_FJm_AbsorptionTrace
import RPu_FJm_RawFrames
import RPu_FJg_HighValue
import RPu_FJg_ScalarValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_SharedCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)

theorem product (partials ap0 ap1 : Array NE 4#usize) (coeff low0 low1 : Array NQ 4#usize)
    (high s0 s1 scale value : NE)
    (cp : FIo_ArrayCanon.Holds partials) (c0 : FIo_ArrayCanon.Holds ap0) (c1 : FIo_ArrayCanon.Holds ap1)
    (cc : FJf_QMArray.canon coeff)
    (hh : FIo_Native.weights.high_dot partials coeff=ok (.Ok high))
    (hs0 : FIo_Native.weights.Weights.scalar_factor low0 ap0=ok s0)
    (hs1 : FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1)
    (hm : FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale)
    (hv : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale high=ok value) :
    FIo_WideValues.Canon value := by
  have ch := (FJg_HighValue.four partials coeff cp cc high hh).1
  have cs0 := (FJg_ScalarValue.value ap0 low0 c0 s0 hs0).1
  have cs1 := (FJg_ScalarValue.value ap1 low1 c1 s1 hs1).1
  have cm := (FIo_WideMulValues.mul s0 s1 scale cs0 cs1 hm).1
  exact (FIo_WideMulValues.mul scale high value cm ch hv).1

theorem value (w : FIo_Install.W) (cf : FJf_FactorArray.canon w.factors)
    (partials ap0 ap1 : Array NE 4#usize)
    (cp : FIo_ArrayCanon.Holds partials) (c0 : FIo_ArrayCanon.Holds ap0) (c1 : FIo_ArrayCanon.Holds ap1)
    (before after : Array NE 7#usize) (cb : FIo_ArrayCanon.Holds before)
    (run : FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after)) :
    FIo_ArrayCanon.Holds after := by
  obtain ⟨row,coeff,low0,low1,high,s0,s1,scale,v1,old,v3',back,
    hr,hd,hh,h0,hs0,h1,hs1,hm,hv,hb,hu⟩ :=
    FJg_SharedHighTrace.reached (FIo_Install.toWeights w) partials ap0 ap1 before after run
  have nr := (FJr_NativeRow.value w cf 0#usize row hr).1
  have cc := nr coeff (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hd))
  have cv1 := product partials ap0 ap1 coeff low0 low1 high s0 s1 scale v1 cp c0 c1 cc hh hs0 hs1 hm hv
  obtain ⟨arow,acoeff,alow0,alow1,ahigh,as0,as1,ascale,v3,base,
    ahr,ahd,ahh,ah0,ahs0,ah1,ahs1,ahm,ahv,ahu⟩ :=
    FJm_AbsorptionTrace.reached (FIo_Install.toWeights w) partials ap0 ap1 before after run
  have anr := (FJr_NativeRow.value w cf 2#usize arow ahr).1
  have acc := anr acoeff (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ ahd))
  have cv3 := product partials ap0 ap1 acoeff alow0 alow1 ahigh as0 as1 ascale v3 cp c0 c1 acc ahh ahs0 ahs1 ahm ahv
  have slot1 : after.val[1]?=some v1 := by
    rw [FJf_ArraySlots.update_slot (back v1) after 3#usize v3' hu 1,if_neg (by decide),
      FIp_ArraySetValue.back before 1#usize old back hb,FJf_ArraySlots.set_slot before 1#usize v1
        (by rw [before.property];change (1:Nat)<7;decide) 1,if_pos (by rfl)]
  have slot3 : after.val[3]?=some v3 := by
    rw [FJf_ArraySlots.update_slot base after 3#usize v3 ahu 3,if_pos (by rfl)]
  intro x hx
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hx
  have slot : after.val[j]?=some x := by rw [List.getElem?_eq_getElem hj,eq]
  by_cases h1 : j=1
  · rw [h1,slot1] at slot
    exact (Option.some.inj slot) ▸ cv1
  · by_cases h3 : j=3
    · rw [h3,slot3] at slot
      exact (Option.some.inj slot) ▸ cv3
    · rw [FJm_RawFrames.shared (FIo_Install.toWeights w) partials ap0 ap1 before after run j
        (by simpa only [show (1#usize).val=1 from by decide] using Ne.symm h1)
        (by simpa only [show (3#usize).val=3 from by decide] using Ne.symm h3)] at slot
      exact cb x (List.mem_of_getElem? slot)

#print axioms product
#print axioms value
end AspisR1.FJr_SharedCanonical
end
