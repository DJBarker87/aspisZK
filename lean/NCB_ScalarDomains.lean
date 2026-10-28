import NBS_DotTerm
import FJl_SlotReads
import FJl_SliceCopy
import JFr_TX2_ScalarCanon
set_option autoImplicit false
noncomputable section
namespace NCB_ScalarDomains
open Aeneas Aeneas.Std Result AspisR1
/-- Derive every scalar decoder domain from the SAME successful slot call.
This is the cohort accepted-run direction; native successful-run association
remains a separate bridge member. -/
theorem accepted (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize)
    (slot : Usize) (out : FIo_Install.NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    NBS_DotTerm.Scalars q slot := by
  obtain ⟨reads,tail⟩ := FJl_SlotReads.reached q g slot out run
  intro term bound
  obtain ⟨selected,value,same,read⟩ := reads term.val bound
  have identical : selected=term := UScalar.eq_of_val_eq same
  subst selected
  obtain ⟨a,window,decode⟩ := FJl_SliceCopy.scalar q slot term value read
  exact ⟨value,read,JFr_TX2_ScalarCanon.source a value decode⟩
#print axioms accepted
end NCB_ScalarDomains
