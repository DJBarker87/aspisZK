import NNH_Run5bPreparedModel
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedInputs
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev sem (s : RSL.Verified LIB_VLib.library) :=
 S1SemanticCarrier.currentSem (LIBC_PreparedCarriers.verified LIB_Prepared.types s)
def view (v : LIB_VCarriers.View) : verifier.View :=
 ⟨InstalledPreparation.currentVariant v.variant,v.semantic,v.y1,
  InstalledPreparation.currentE v.inactive,v.round0,v.folded_root,v.round1,v.final_message,v.query_bytes⟩
abbrev scratch (g : LIB_VCarriers.E29) :=
 AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE g

theorem semantic (s : RSL.Verified LIB_VLib.library) :
 InstalledPreparation.retainedSem (sem s) = LIBC_PreparedCarriers.verified LIB_Prepared.types s :=
 S1SemanticCarrier.semantic_round _

theorem field (e : AspisR1PublicPreparation.aspis_core.field.WideExact) :
 InstalledPreparation.retainedE (InstalledPreparation.currentE e) = e := by cases e; rfl

theorem view_input (v : LIB_VCarriers.View) : InstalledPreparation.retainedView (view v)=v := by
 cases v with
 | mk variant semantic y1 inactive round0 root round1 final_ query =>
  cases variant <;> rfl

theorem scratch_input (g : LIB_VCarriers.E29) :
 AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.retainedE (scratch g)=g := by
 apply Subtype.ext
 change (g.val.map InstalledPreparation.currentE).map InstalledPreparation.retainedE = g.val
 simp only [List.map_map,Function.comp_def,field]
 exact List.map_id _
#print axioms semantic
#print axioms field
#print axioms view_input
#print axioms scratch_input
end AspisR1.NNV_PreparedInputs
end
