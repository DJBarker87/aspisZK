import NJF_FinishObserved
import NJU_WeakPairCaller
import NJU_WeakPairInstantiation
import NJU_WeakPairInstalled
import NJU_WeakFinishComposedLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakFinishObserved
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition
open NIW_AlignFinishComposed Classical
open NJF_FinishObserved

/- Generalized existing evaluator on arbitrary raw words; data/log definitions reused. -/
theorem detail_source (r : NP6_StdModel.Reservation) (loc : Locations) (owner : FIo_Install.W)
 (v : verifier.View) (p : verifier.Prepared)
 (domain : NJU_WeakPairDomain.Domain (FIo_Install.toWeights owner)
  (NFW_PowersCohort.mapArray FIo_Install.toE p.alpha) v.final_message (FIo_Install.toE p.kappa)) :
 detailG r loc owner v p=detail r loc owner v p := by
 unfold detailG
 rw [NJU_WeakPairInstantiation.source r _ domain]
 rfl

/-- Whole observation identity, including all entered abort prefixes and all
nested pair information. No endpoint or child-success premise is retained. -/

theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NJU_FinishInput.Holds proof v p a) : G r loc v p a=run r loc v p a := by
 unfold G run
 apply observe_congr
 intro first firstCall
 apply observe_congr
 intro claim claimCall
 apply observe_congr
 intro owner newCall
 have caller:=NJU_WeakPairCaller.caller r proof v p a domain owner newCall
 rw [NJU_WeakFinishObserved.detail_source r loc owner v p caller]

/-- The complete source event list and complete returned Result, not only the
acceptance decision, follow from the full source erasure already proved by NIW. -/

theorem source_log (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NJU_FinishInput.Holds proof v p a) :
 NIW_AlignFinishComposedLog.forget (G r loc v p a)=NIW_AlignFinishExecution.run r v p a := by
 rw [source r loc proof v p a domain]
 exact NJU_WeakFinishComposedLog.source r loc proof v p a domain

#print axioms detail_source
#print axioms source
#print axioms source_log
end AspisR1.NJU_WeakFinishObserved
