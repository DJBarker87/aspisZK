import NNG_ProjectMaskArrays
import NNG_ModelMask
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectMaskDomain
open Aeneas Aeneas.Std Result NNG_Emitted NNG_Transport NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain
open AspisR1.NMT_Transport (arr)

theorem map_project {n : Usize} (fallback : Value) (a : Array Q n) :
    LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw (projectArray fallback a) =
      arr (fun q => LIB_VScalarCarriers.toRaw (project fallback q)) a := by
  apply Subtype.ext
  simp only [LIB_VScalarCarriers.array,projectArray,arr,List.map_map,Function.comp_def]
#print axioms map_project

/-- Only the 16+10+1 cells actually passed to the mask are required canonical.
Unused claims cells are unrestricted and cannot become caller conditions. -/
theorem call_model (fallback : Value) (claims : Claims) (alpha : Alpha)
    (lowDom : DomainArray (NNG_FromFnValues136.low claims))
    (highDom : DomainArray (NNG_FromFnValues136.high claims))
    (blindDom : Domain (NNG_Array136.cell claims 27#usize (by decide))) (alphaDom : DomainArray alpha) :
    NNG_ModelMask.call (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims)
      (NNG_Array136.cell claims 27#usize (by decide)) alpha =
      .ok (lower (LIB_VField.maskValue (projectClaims fallback claims) (projectArray fallback alpha))) := by
  have low := (NNG_ProjectMaskCells.raw_array fallback _ lowDom).trans
    ((map_project fallback _).trans (NNG_ProjectMaskArrays.low fallback claims))
  have high := (NNG_ProjectMaskCells.raw_array fallback _ highDom).trans
    ((map_project fallback _).trans (NNG_ProjectMaskArrays.high fallback claims))
  have blind : toT1 (NNG_Array136.cell claims 27#usize (by decide)) = LIB_VField.g (projectClaims fallback claims) :=
    (NNG_LIBField.raw_project fallback _ blindDom).symm.trans
      (congrArg LIB_VScalarCarriers.toRaw (NNG_ProjectMaskCells.cell fallback claims 27#usize (by decide))).symm
  have alphaRaw := NNG_ProjectMaskCells.raw_array fallback alpha alphaDom
  unfold NNG_ModelMask.call
  rw [low,high,blind,alphaRaw]
  change NMP_ResultTransport.outer fromT1
    (FIp_SemanticArithmetic.mask (LIB_VField.c1 (projectClaims fallback claims))
      (LIB_VField.maskOnly (projectClaims fallback claims)) (LIB_VField.g (projectClaims fallback claims))
      (LIB_VCarriers.alphaRaw (projectArray fallback alpha))) = _
  rw [LIB_VField.mask_exact]
  rfl
#print axioms call_model

theorem returned (fallback : Value) (claims : Claims) (alpha : Alpha) (q : Q)
    (lowDom : DomainArray (NNG_FromFnValues136.low claims))
    (highDom : DomainArray (NNG_FromFnValues136.high claims))
    (blindDom : Domain (NNG_Array136.cell claims 27#usize (by decide))) (alphaDom : DomainArray alpha)
    (success : NNG_ModelMask.call (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims)
      (NNG_Array136.cell claims 27#usize (by decide)) alpha = .ok q) : Domain q := by
  have same := Result.ok.inj ((call_model fallback claims alpha lowDom highDom blindDom alphaDom).symm.trans success)
  rw [←same]
  exact lower_domain _
#print axioms returned
end AspisR1.NNG_ProjectMaskDomain
