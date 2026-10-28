import NDO_JGp_Prepare
import NDO_JGp_ValuesIdentity
import RPz8_F3R_PrepareBuffers
import RPz7_SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_PrepareCuts
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation
open AspisR1PublicPreparation.PreparedHashCode

def inner {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) : Ops :=
  Op3I_Install.install (Op4P_Install.install (WAdm_Execution.base base true query geo))

/-- This is an inversion of the SAME enclosing prepare return. Both expansion
operands and the returned scratch are retained from its actual cuts. -/
theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (JGp_PrepareLayout.installed base query geo)
      D public1 JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    ∃ (initial expanded : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      AspisS1NativeCompact.compact.expand_semantic nativeValues JFw_RealExpansion.stored initial=ok (.Ok (),expanded) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
        D public1 expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash input=ok (.Ok p,scratch) := by
  let raw := inner base query geo
  let std := NP6_StdModel.calls (.Ok ())
  let B := JGe_Boundaries.value
  have erased := (SdkD_PrepareSource.source raw B std D public1 JFx_NativeBytes.proof hash input).trans success
  obtain ⟨semantic,y1,view,sem,wide,semanticCode,originalCode,logs,
    off0,off1,off2,stored,initial,expanded,storedY1,initialY1,expandedY1,
    h0,h1,h2,read,expand,readY1,expandY1,semanticEq,y1Eq⟩ :=
    F3R_PrepareBuffers.reached raw AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
      D public1 JFx_NativeBytes.proof hash p input scratch
      (fun a b c d call=>AspisS1NativeCompactLengths.semantic_length nativeValues a b d c call)
      (fun a b c d call=>length_frame a b d c call) erased
  have e0 : off0=16#usize := Result.ok.inj (h0.symm.trans (JGp_PrepareLayout.semantic base query geo))
  have e1 : off1=7031#usize := Result.ok.inj (h1.symm.trans (JGp_PrepareLayout.offsetY1 base query geo))
  have e2 : off2=7495#usize := Result.ok.inj (h2.symm.trans (JGp_PrepareLayout.inactive base query geo))
  subst off0 off1 off2
  have storedEq : stored=JFw_RealExpansion.stored := Result.ok.inj (read.symm.trans JGp_PrepareReads.semantic)
  have yStoredEq : storedY1=JFw_Y1.stored := Result.ok.inj (readY1.symm.trans JGp_PrepareReads.y1)
  subst stored storedY1
  have ey := JGp_ValuesIdentity.source initialY1 expandedY1 expandY1
  subst semantic y1 expandedY1
  have verify := (S1SemanticCodeInstallation.source AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D public1 view.semantic hash).symm.trans semanticCode
  have prepared := (closedPreparationCode_erasure D sem view hash input).symm.trans originalCode
  have viewsem := sourceView_semantic _ _ _ _ wide
  rw [viewsem] at verify
  exact ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,prepared⟩
#print axioms source
end AspisR1.JGp_PrepareCuts
end
