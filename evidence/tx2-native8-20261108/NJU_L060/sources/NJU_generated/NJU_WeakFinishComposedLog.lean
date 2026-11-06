import NIW_AlignFinishComposedLog
import NJU_WeakPairCaller
import NJU_WeakPairInstantiation
import NJU_WeakPairInstalled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakFinishComposedLog
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2
open NIW_AlignFinishComposed
open NIW_AlignFinishComposedLog

/- Generalized existing evaluator on arbitrary raw words; data/log definitions reused. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NJU_FinishInput.Holds proof v p a) :
 forget (run r loc v p a)=NIW_AlignFinishExecution.run r v p a := by
 rw [run,forget_observe,NIW_AlignFinishExecution.run]
 apply observe_congr
 intro first firstCall
 rw [forget_observe]
 apply observe_congr
 intro claim claimCall
 rw [forget_observe]
 apply observe_congr
 intro owner newCall
 have caller := NJU_WeakPairCaller.caller r proof v p a domain owner newCall
 have native := (NJU_WeakPairInstalled.source r ⟨loc.owner,owner⟩ ⟨loc.alpha,p.alpha⟩
  ⟨loc.message,v.final_message⟩ p.kappa loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts caller).1
 have pairLaw : NIT_ErrorTransport.full (detail r loc owner v p).native.1=
  FIo_Install.pair r owner p.alpha.to_slice v.final_message p.kappa := native.symm
 dsimp only
 rw [forget_attach,forget_observe,pairLaw,NIG_PairInputs.alpha_prefix]
 apply observe_congr
 intro value pairCall
 split
 · rfl
 · rw [forget_observe]
   apply observe_congr
   intro actual dotCall
   rfl

#print axioms source
end AspisR1.NJU_WeakFinishComposedLog
