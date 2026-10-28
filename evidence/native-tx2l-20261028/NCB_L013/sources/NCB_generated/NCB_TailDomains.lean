import NCB_TailOffsets
import FJl_SlotReads
set_option autoImplicit false
noncomputable section
namespace NCB_TailDomains
open Aeneas Aeneas.Std Result AspisR1
/-- All three actual decoder domains follow from THIS successful slot call.
No independently successful tail execution or final dot value is assumed. -/
theorem accepted (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize)
    (s : Fin 4) (out : FIo_Install.NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g (NCB_TailOffsets.slot s)=ok out) :
    NBS_DotTail.Domain q s := by
  obtain ⟨reads,q0,q1,q2,h0,h1,h2⟩ := FJl_SlotReads.reached q g (NCB_TailOffsets.slot s) out run
  rw [NCB_TailOffsets.first] at h0
  rw [NCB_TailOffsets.second] at h1
  rw [NCB_TailOffsets.third] at h2
  intro kind
  fin_cases kind
  · exact ⟨q0,h0⟩
  · exact ⟨q1,h1⟩
  · exact ⟨q2,h2⟩
#print axioms accepted
end NCB_TailDomains
end
