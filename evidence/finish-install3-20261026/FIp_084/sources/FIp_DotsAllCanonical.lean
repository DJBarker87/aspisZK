import FIp_DotsCanonical
import FIo_ArrayCanon
import FIp_DotsReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsAllCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem four (q : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) : FIo_ArrayCanon.Holds out := by
  obtain ⟨selected,prefix608,v0,v1,v2,v3,converted,hs,hc,hp,h0,h1,h2,h3,he⟩ := FIp_DotsReached.four q g out run
  subst out
  intro x hx
  simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact FIp_DotsCanonical.helper prefix608 g 0#usize v0 h0
  · exact FIp_DotsCanonical.helper prefix608 g 1#usize v1 h1
  · exact FIp_DotsCanonical.helper prefix608 g 2#usize v2 h2
  · exact FIp_DotsCanonical.helper prefix608 g 3#usize v3 h3

#print axioms four
end AspisR1.FIp_DotsAllCanonical
end
