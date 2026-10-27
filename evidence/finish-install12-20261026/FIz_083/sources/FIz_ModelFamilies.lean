import FIy_NativeCoefficients
import FIy_ValueFamilyList
import FIz_ScheduleFamily
import FIz_PathFamily
import FIz_OccupancyFamily
import FIz_DigestFamily
import FIz_ScalarList
import FIz_ContributionAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ModelFamilies
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
attribute [local irreducible] FIz_ContributionList.fromList

theorem value (p : Public) (o : Openings) (s : Selectors) (j : Fin (24#usize).val)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIy_NativeCoefficients.model p o s j=
      FIz_ContributionList.fromList (R0P.scheduleFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 0 j.val+
      FIz_ContributionList.fromList (R0P.pathFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 32 j.val+
      FIz_ContributionList.fromList (R0P.valueFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 49 j.val+
      FIz_ContributionList.fromList (R0P.digestFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 84 j.val+
      FIz_ContributionList.fromList (R0P.assetFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 92 j.val+
      FIz_ContributionList.fromList (R0P.occupancyFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s)) 0 j.val := by
  unfold FIy_NativeCoefficients.model
  simp only [FIz_ContributionList.value]
  have schedule := FIz_ContributionAppend.value (List.ofFn (FIx_ScheduleModel.initial p.variant s o))
    (List.ofFn (FIx_ScheduleModel.absorption p.variant s o)) 0 j.val
  simp only [List.length_ofFn] at schedule
  have values := FIz_ContributionAppend.value (List.ofFn (FIy_ValuePacked.rangeModel o s))
    (List.ofFn (FIy_ValuePacked.conservation o s)) 49 j.val
  simp only [List.length_ofFn] at values
  rw [FIz_ScheduleFamily.value p o s hm lm] at schedule
  rw [FIy_ValueFamilyList.value p o s] at values
  rw [FIz_PathFamily.value p o s hm lm,FIz_OccupancyFamily.value p o s,
    FIz_DigestFamily.value p o s,FIz_ScalarList.value p o s]
  have shift16 : FIz_ContributionList.fromList (List.ofFn (FIx_ScheduleModel.absorption p.variant s o))
      (0+(16#usize).val) j.val=FIz_ContributionList.fromList (List.ofFn (FIx_ScheduleModel.absorption p.variant s o)) 16 j.val := rfl
  have shift82 : FIz_ContributionList.fromList (List.ofFn (FIy_ValuePacked.conservation o s))
      (49+(33#usize).val) j.val=FIz_ContributionList.fromList (List.ofFn (FIy_ValuePacked.conservation o s)) 82 j.val := rfl
  rw [shift16] at schedule
  rw [shift82] at values
  rw [schedule,values]
  ring
#print axioms value
end AspisR1.FIz_ModelFamilies
end
