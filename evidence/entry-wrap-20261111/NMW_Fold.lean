import NMW_RowSpecs
set_option autoImplicit false
noncomputable section
namespace NMW_Fold
open Aeneas Aeneas.Std AspisR1 NMW_Outcome NMW_FullDispatch NMW_RowSpecs
/-- Parameterized fold ONLY: not a candidate/root until both full child
packets and each own-input caller clause are instantiated with their owners. -/
theorem process_fold {A W E : Type} (native model : Children A W E)
 (parentDomain firstDomain secondDomain : Args A → W → Prop)
 (stage1 : RowSpec_344 native.first model.first firstDomain)
 (stage2 : RowSpec_240 native.second model.second secondDomain)
 (caller1 : CallerClause Hiq_ReleaseRoute.stage1 parentDomain firstDomain)
 (caller2 : CallerClause Hiq_ReleaseRoute.asq8 parentDomain secondDomain) :
 ProcessSpec native model parentDomain := by
 intro args before parent route
 rcases route with one | two
 · rw [process_first native args before one,process_first model args before one]
   exact stage1 args before (caller1 args before parent one)
 · rw [process_second native args before two,process_second model args before two]
   exact stage2 args before (caller2 args before parent two)
/-- Both routes and reject arm in ONE shared frozen entry fold. Rejection
preserves the entire input world and produces no child/runtime event. -/
theorem entry_fold {A W E : Type} (native model : Children A W E)
 (parentDomain firstDomain secondDomain : Args A → W → Prop)
 (stage1 : RowSpec_344 native.first model.first firstDomain)
 (stage2 : RowSpec_240 native.second model.second secondDomain)
 (caller1 : CallerClause Hiq_ReleaseRoute.stage1 parentDomain firstDomain)
 (caller2 : CallerClause Hiq_ReleaseRoute.asq8 parentDomain secondDomain) :
 EntrySpec native model parentDomain := by
 intro args before parent
 rw [entry_total,entry_total]
 cases selected : Hiq_ReleaseRoute.route args.data with
 | first =>
   exact stage1 args before (caller1 args before parent
     ((Hiq_ReleaseRoute.first_iff args.data).mp selected))
 | second =>
   exact stage2 args before (caller2 args before parent
     ((Hiq_ReleaseRoute.second_iff args.data).mp selected).2)
 | reject => rfl
#print process_fold
#print entry_fold
#print axioms process_fold
#print axioms entry_fold
end NMW_Fold
end
