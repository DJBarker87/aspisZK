import NNG_PreparedGraph087
import NNG_FinishOccurrence137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedReturned094
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
/-- The actual returned call supplies the CLOSED law observation at its SAME
semantic/View/scratch inputs, including its own chronological digest prefix. -/
theorem law (env : RSL.Env) (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (before g : NMP_Emitted.Scratch) (p : verifier.Prepared)
 (native : NNG_PreparedCall087.call (NNG_PublicSource137.digest env) sem v () before=.ok (.Ok p,g)) :
 ∃ ev,LIBC_PreparedLaw.law (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,
  NMT_Transport.arr NNG_PrepareCarriers087.wide before) env
  ⟨.ret (.ok (NNG_PrepareCarriers087.prepared p),NMT_Transport.arr NNG_PrepareCarriers087.wide g),ev⟩ := by
 have checked := NNG_PreparedGraph087.law env sem v before
 unfold NNG_Observed136.observation at checked
 rw [NNG_FinishOccurrence137.run_invoke,native] at checked
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,NNG_Events087.prepared_call] at checked
 exact ⟨_,checked⟩
#print axioms law
end AspisR1.NNG_PreparedReturned094
