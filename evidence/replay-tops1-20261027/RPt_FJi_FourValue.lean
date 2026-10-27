import RPt_FJi_SlotValue
import RPt_FJi_PrefixValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_FourValue
open Aeneas Aeneas.Std Result
open FJi_Accumulations
/-- All four native slots, on the SAME source-selected first608 opening bytes. -/
theorem value (q : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (hg : FIo_ArrayCanon.Holds g)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) :
    ∃ opening608 : Array U8 608#usize,opening608.val=q.val.take 608 ∧
      ∀ slot : Fin 4,FIp_ArrayValue.value out slot.val=
        FJi_SlotValue.model opening608 g (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) := by
  obtain ⟨selected,opening608,v0,v1,v2,v3,converted,hs,hc,hp,h0,h1,h2,h3,ho⟩ :=
    FIp_DotsReached.four q g out run
  refine ⟨opening608,(FJi_PrefixValue.array selected opening608 converted hc hp).trans
    (FJi_PrefixValue.selected q selected hs),?_⟩
  subst out
  intro slot
  fin_cases slot
  · exact (FJi_SlotValue.value opening608 g 0#usize v0 hg h0).2
  · exact (FJi_SlotValue.value opening608 g 1#usize v1 hg h1).2
  · exact (FJi_SlotValue.value opening608 g 2#usize v2 hg h2).2
  · exact (FJi_SlotValue.value opening608 g 3#usize v3 hg h3).2
#print axioms value
end AspisR1.FJi_FourValue
end
