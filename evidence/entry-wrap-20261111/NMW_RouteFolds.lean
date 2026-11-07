import NMW_EntryFold
set_option autoImplicit false
noncomputable section
namespace NMW_RouteFolds
open Aeneas Aeneas.Std AspisR1 NMW_Outcome NMW_FullDispatch NMW_RowSpecs
/-- TX1:333 intermediate fold: only its REAL stage1 dependency is required.
The other route's OPEN child never blocks this occurrence. -/
theorem process_tx1 {A W E : Type} (native model : Children A W E)
 (parentDomain childDomain : Args A → W → Prop)
 (stage1 : RowSpec_344 native.first model.first childDomain)
 (caller : CallerClause Hiq_ReleaseRoute.stage1 parentDomain childDomain)
 (input : Args A) (before : W) (own : parentDomain input before)
 (route : Hiq_ReleaseRoute.stage1 input.data) :
 process native input before = process model input before := by
 rw [process_first native input before route,process_first model input before route]
 exact stage1 input before (caller input before own route)
/-- TX2:221 intermediate fold, independently of344. -/
theorem process_tx2 {A W E : Type} (native model : Children A W E)
 (parentDomain childDomain : Args A → W → Prop)
 (stage2 : RowSpec_240 native.second model.second childDomain)
 (caller : CallerClause Hiq_ReleaseRoute.asq8 parentDomain childDomain)
 (input : Args A) (before : W) (own : parentDomain input before)
 (route : Hiq_ReleaseRoute.asq8 input.data) :
 process native input before = process model input before := by
 rw [process_second native input before route,process_second model input before route]
 exact stage2 input before (caller input before own route)
/-- TX1:330 follows its actual process child, with no240 premise. -/
theorem entry_tx1 {A W E : Type} (native model : Children A W E)
 (parentDomain childDomain : Args A → W → Prop)
 (stage1 : RowSpec_344 native.first model.first childDomain)
 (caller : CallerClause Hiq_ReleaseRoute.stage1 parentDomain childDomain)
 (input : Args A) (before : W) (own : parentDomain input before)
 (route : Hiq_ReleaseRoute.stage1 input.data) :
 entry native input before = entry model input before := by
 rw [NMW_EntryFold.admitted native input before (Or.inl route),
     NMW_EntryFold.admitted model input before (Or.inl route)]
 exact process_tx1 native model parentDomain childDomain stage1 caller input before own route
/-- TX2:213 follows its actual process child, with no344 premise. -/
theorem entry_tx2 {A W E : Type} (native model : Children A W E)
 (parentDomain childDomain : Args A → W → Prop)
 (stage2 : RowSpec_240 native.second model.second childDomain)
 (caller : CallerClause Hiq_ReleaseRoute.asq8 parentDomain childDomain)
 (input : Args A) (before : W) (own : parentDomain input before)
 (route : Hiq_ReleaseRoute.asq8 input.data) :
 entry native input before = entry model input before := by
 rw [NMW_EntryFold.admitted native input before (Or.inr route),
     NMW_EntryFold.admitted model input before (Or.inr route)]
 exact process_tx2 native model parentDomain childDomain stage2 caller input before own route
#print axioms process_tx1
#print axioms process_tx2
#print axioms entry_tx1
#print axioms entry_tx2
end NMW_RouteFolds
end
