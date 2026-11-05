import NIG_NewDomain
set_option autoImplicit false
namespace NIG_NewReply
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NGW_ConstructorArrays

theorem inner (alpha:Array K 10#usize)
 (z:Array aspis_core.circle.SecureCirclePoint 2#usize) (w:FIn_WeightsExtract.Weights)
 (run:FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) :
 FIn_WeightsExtract.weights_new .S2 (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)
  (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z)=ok (.Ok w) := by
 unfold FIn_WeightsInstall.newWeights at run
 obtain ⟨reply,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases reply with
 | Err e=>cases e;cases run
 | Ok out=>
  cases core.result.Result.Ok.inj (Result.ok.inj run)
  exact hr

/-- The caller obtains pair's domain from the SAME successful NEW reply. The
Err and nonreturn arms remain in the enclosing full-Result driver. -/
theorem returned (alpha:Array K 10#usize)
 (z:Array aspis_core.circle.SecureCirclePoint 2#usize)
 (ha:Holds NGW_NewInterface.CanonK alpha)
 (hz:Holds (fun point=>NGW_NewInterface.CanonK point.x ∧ NGW_NewInterface.CanonK point.y) z)
 (w:FIn_WeightsExtract.Weights)
 (run:FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) :
 (FIo_Install.toWeights w).variant=FIo_Native.transport.Variant.S2 ∧
 NHI_TensorOuterStep.Factors (FIo_Install.toWeights w) ∧
 NHI_CellCanon.array (FIo_Install.toWeights w).extra := by
 obtain ⟨produced,source,cf,cp,ce⟩:=NGW_NewInterface.cohort .S2 alpha z ha hz
 have same:=core.result.Result.Ok.inj (Result.ok.inj (source.symm.trans run))
 cases same
 have variant:=NIG_NewDomain.variant .S2 _ _ w (inner alpha z w run)
 refine ⟨?_,NIG_NewDomain.factors w cf,NIG_NewDomain.extra w ce⟩
 change FIo_Install.variant w.variant=FIo_Native.transport.Variant.S2
 rw [variant]
 rfl
#print axioms inner
#print axioms returned
end NIG_NewReply
