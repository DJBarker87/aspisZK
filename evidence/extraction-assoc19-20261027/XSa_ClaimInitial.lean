import XSa_PointRun
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XSa_ClaimInitial
open AspisR1ClaimPreparedBridge

def initial (inactive : C.E) : Seven := (Array.repeat 7#usize XRy_Powers.zero).set 0#usize inactive

theorem front (inactive : C.E) : (initial inactive).val.take 1=[inactive] := by
 exact XSa_ArrayPrefix.write (Array.repeat 7#usize XRy_Powers.zero) 0#usize inactive (by scalar_tac)

theorem canonical (inactive : C.E) (hi : XRy_WideMultiply.Canonical inactive) :
 XRy_ClaimSumStep.canonical (initial inactive) := by
 apply XSa_ArraySeven.canonical_set _ _ _ (by scalar_tac) inactive hi
 intro i hi
 unfold cell
 simp only [Array.repeat,List.getElem_replicate]
 exact XRy_ClaimSum.zero_canonical

theorem actual (inactive : C.E) :
 Array.update (Array.repeat 7#usize AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.ZERO)
   0#usize (toClaimE inactive)=ok (arr toClaimE (initial inactive)) := by
 rw [←XRy_ClaimSum.zero_claim,←XRy_ArrayMap.repeated]
 rw [XSa_ArraySeven.update _ _ _ (by scalar_tac),←XRy_ArrayMap.set]
 rfl

#print axioms front
#print axioms canonical
#print axioms actual
end XSa_ClaimInitial
