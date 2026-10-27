import RPt_FJo_FourCalls
import RPt_FJo_C1SlotDecode
import RPt_FJo_C2SlotDecode
import RPt_FJo_PrefixBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_OpeningDecodes
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- Complete strict C1/C2 decodes follow from THIS backend success. -/
theorem value (opening : Slice U8) (g : Array FIo_Install.NE 29#usize)
    (out : Array FIo_Install.NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots opening g=ok out) :
    (∃ c1,MixedLeafDecoder.decodeC1 ((bytesOf opening.val).take 480)=some c1) ∧
    (∃ c2,MixedLeafDecoder.decodeC2 (((bytesOf opening.val).drop 480).take 128)=some c2) := by
  obtain ⟨selected,q,converted,hs,hc,hp,calls⟩ := FJo_FourCalls.reached opening g out run
  have bytes := FJo_PrefixBytes.value opening selected q converted hs hc hp
  have qlen : q.val.length=608 := q.property
  have len1 : ((bytesOf q.val).take 480).length=120*4 := by
    simp only [bytesOf,List.length_take,List.length_map,qlen];omega
  have len2 : (((bytesOf q.val).drop 480).take 128).length=32*4 := by
    simp only [bytesOf,List.length_take,List.length_drop,List.length_map,qlen];omega
  have c1 := FJo_FixedAssemble.value MixedLeafDecoder.decodeC1Slot 120 4 ((bytesOf q.val).take 480) len1 (by
    intro s
    obtain ⟨v,run,read⟩ := calls s
    exact FJo_C1SlotDecode.value q g s _ rfl v run)
  have c2 := FJo_FixedAssemble.value MixedLeafDecoder.decodeC2Slot 32 4 (((bytesOf q.val).drop 480).take 128) len2 (by
    intro s
    obtain ⟨v,run,read⟩ := calls s
    exact FJo_C2SlotDecode.value q g s _ rfl v run)
  change (∃ c1,MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c1) at c1
  change (∃ c2,MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c2) at c2
  rw [bytes,List.take_take] at c1
  rw [bytes,List.drop_take,List.take_take] at c2
  exact ⟨c1,c2⟩
#print axioms value
end AspisR1.FJo_OpeningDecodes
end
