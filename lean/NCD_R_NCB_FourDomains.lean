-- Retargeted inherited proof body; only module imports changed.
import NCD_R_NCB_ScalarDomains
import NCD_R_NCB_TailDomains
import RPu_FJo_FourCalls
set_option autoImplicit false
noncomputable section
namespace NCB_FourDomains
open Aeneas Aeneas.Std Result AspisR1
/-- Derive all four scalar/tail caller domains from one SAME full source
return, keeping its selected608-byte carrier and each output slot linked. -/
theorem accepted (opening : Slice U8) (g : Array FIo_Install.NE 29#usize)
    (out : Array FIo_Install.NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots opening g=ok out) :
    ∃ q : Array U8 608#usize,
      ∀ s : Fin 4, ∃ value,
        FIp_NativeDots.fast_dots.four_dots_one q g (NCB_TailOffsets.slot s)=ok value ∧
        out.val[s.val]?=some value ∧
        NBS_DotTerm.Scalars q (NCB_TailOffsets.slot s) ∧ NBS_DotTail.Domain q s := by
  obtain ⟨selected,q,converted,range,conversion,unwrap,calls⟩ := FJo_FourCalls.reached opening g out run
  refine ⟨q,?_⟩
  intro s
  obtain ⟨value,call,slot⟩ := calls s
  exact ⟨value,call,slot,NCB_ScalarDomains.accepted q g _ value call,
    NCB_TailDomains.accepted q g s value call⟩
#print axioms accepted
end NCB_FourDomains
end
