import JFs_TX2_Slot
import JFs_TX2_FourHead
import FIp_DotsAllCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Four
open Aeneas Aeneas.Std Result

theorem source (i : Fin 12) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value (JFn_Values.position i))
      JFr_TX2_FirstLane.native=ok out ∧ FIo_ArrayCanon.Holds out := by
  obtain ⟨a,h0,_⟩ := JFs_TX2_Slot.source i 0
  obtain ⟨b,h1,_⟩ := JFs_TX2_Slot.source i 1
  obtain ⟨c,h2,_⟩ := JFs_TX2_Slot.source i 2
  obtain ⟨d,h3,_⟩ := JFs_TX2_Slot.source i 3
  let out : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,b,c,d]
  have run : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value (JFn_Values.position i))
      JFr_TX2_FirstLane.native=ok out := by
    rw [JFs_TX2_FourHead.source]
    simp only [JFs_TX2_FourHead.slots,h0,h1,h2,h3,bind_tc_ok]
    rfl
  exact ⟨out,run,FIp_DotsAllCanonical.four _ _ out run⟩

#print axioms source
end AspisR1.JFs_TX2_Four
end
