import JHe_CurrentWriterImage
import JHa_CurrentFields
import JHa_CurrentRho
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_PreparedScalarBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

/-- The actual writer's early scalar fields, byte for byte. The preparation
is the actual returned preparation, not a fixture supplied as an operand. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (WAdm_SourceBody.put (prepared p).gamma).map CheckpointBytes5Writer.u8=JFq_Gamma.bytes ∧
    (WAdm_SourceBody.put (prepared p).kappa).map CheckpointBytes5Writer.u8=JFq_Kappa.bytes ∧
    ((prepared p).alpha.val.flatMap WAdm_SourceBody.put).map CheckpointBytes5Writer.u8=
      JFq_Alpha0.bytes++JFq_Alpha1.bytes ∧
    (WAdm_SourceBody.putK (prepared p).rho).map CheckpointBytes5Writer.u8=JFq_Rho.bytes := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  change (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.gamma))).map _=_ ∧
    (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.kappa))).map _=_ ∧
    (((Tx1Q_Carriers.arr Tx1Q_Carriers.e p.alpha).val.map CheckpointBytes3Namespaces.toE).flatMap
      WAdm_SourceBody.put).map _=_ ∧
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k p.rho))).map _=_
  rw [fields.1,fields.2.1,fields.2.2,rho.1]
  exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms source
end AspisR1.JHk_PreparedScalarBytes
end
