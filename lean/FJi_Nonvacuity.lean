import FJi_MatchingMeaning
import JFs_TX2_Dots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Nonvacuity
open Aeneas Aeneas.Std Result

theorem powers : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray JFr_TX2_Powers.value) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hy
  have hi : n < 29 := by
    rw [JFr_TX2_Powers.value.property] at hn
    have v29 : (29#usize).val=29 := by scalar_tac
    simpa only [v29] using hn
  have hc := JFr_TX2_Powers.canonical ⟨n,hi⟩
  simpa only [eq] using hc

/-- The universal backend VALUE premise has a retained successful native fixture.
This is local non-vacuity, not an unconditional deployed security fixture. -/
theorem value (i : Fin 12) :
    ∃ opening608 : Array U8 608#usize,
      opening608.val=(JFo_Opening.value (JFn_Values.position i)).val.take 608 ∧
      FIp_DotsAdapter.dots (JFo_Opening.value (JFn_Values.position i)) JFr_TX2_Powers.value=
        ok (JFs_TX2_Dots.value i) ∧
      ∀ slot : Fin 4,Port5Q1_OpeningValues.values (JFs_TX2_Dots.value i) slot=
        FJi_SlotValue.model opening608 (FIp_DotsAdapter.toArray JFr_TX2_Powers.value)
          (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) := by
  obtain ⟨opening608,hp,values⟩ := FJi_MatchingMeaning.value _ _ _ powers (JFs_TX2_Dots.adapter i)
  exact ⟨opening608,hp,JFs_TX2_Dots.adapter i,values⟩
#print axioms powers
#print axioms value
end AspisR1.FJi_Nonvacuity
end
