import RPu_FJi_ArrayAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_MatchingMeaning
open Aeneas Aeneas.Std Result
abbrev E := FIp_DotsAdapter.E
/-- Complete installed dot VALUE. The opening608 is constrained to the SAME actual
opening, and every slot uses the SAME actual selected width29 powers. This
is the backend meaning, not yet the model's match0 or L143 theorem. -/
theorem value (q : Slice U8) (g : Array E 29#usize) (out : Array E 4#usize)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (run : FIp_DotsAdapter.dots q g=ok out) :
    ∃ opening608 : Array U8 608#usize,opening608.val=q.val.take 608 ∧
      ∀ slot : Fin 4,Port5Q1_OpeningValues.values out slot=
        FJi_SlotValue.model opening608 (FIp_DotsAdapter.toArray g)
          (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) := by
  obtain ⟨native,hn,he⟩ := FIp_DotsAdapter.reached q g out run
  obtain ⟨opening608,hp,values⟩ := FJi_FourValue.value q (FIp_DotsAdapter.toArray g) native hg hn
  refine ⟨opening608,hp,?_⟩
  subst out
  intro slot
  rw [FJi_ArrayAdapter.values]
  exact values slot
#print axioms value
end AspisR1.FJi_MatchingMeaning
end
