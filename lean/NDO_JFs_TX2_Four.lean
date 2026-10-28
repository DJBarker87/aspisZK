import NDO_JFs_TX2_Slot
import NDO_JFs_TX2_FourHead
import RPt_FIp_DotsAllCanonical
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
  have z0 : Usize.ofNat ((0:Fin 4).val) (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z0] at h0
  have z1 : Usize.ofNat ((1:Fin 4).val) (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z1] at h1
  have z2 : Usize.ofNat ((2:Fin 4).val) (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z2] at h2
  have z3 : Usize.ofNat ((3:Fin 4).val) (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [z3] at h3
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
