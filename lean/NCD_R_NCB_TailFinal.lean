-- Retargeted inherited proof body; only module imports changed.
import NCD_R_JFs_TX2_WideAdd
import NBQ_U06
set_option autoImplicit false
noncomputable section
namespace NCB_TailFinal
open Aeneas Aeneas.Std Result AspisR1
/-- Finish and final addition use THIS tail state, and the same returned
finish value. There is no independently chosen successful final dot call. -/
theorem source (value : FIo_Install.NE) (canonical : FIo_WideValues.Canon value)
    (tail : FIo_Native.fast_pairing.EbyKDot) :
    ∃ finished out,
      FIo_Native.fast_pairing.EbyKDot.finish tail=ok finished ∧
      FIo_WideValues.Canon finished ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.add value finished=ok out ∧
      FIo_WideValues.Canon out := by
  obtain ⟨finished,finish,domain⟩ := NBQ_U06.finish tail
  obtain ⟨out,add,canon⟩ := JFs_TX2_WideAdd.source value finished canonical domain
  exact ⟨finished,out,finish,domain,add,canon⟩
#print axioms source
end NCB_TailFinal
end
