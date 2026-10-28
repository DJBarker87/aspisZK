import NDO_JHc_QueryPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_PowerInputs
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open CheckpointBytes5Output (ofK)
attribute [local irreducible] JGp_Seeds.base JGp_Seeds.query JGp_Seeds.geometry
  JFx_NativeBytes.proof JFx_NativeBytes.publicInput

/-- Numeric identity for the actual TX1 query result, independent of the
flush and writer. The final result is an operand, never an assumed identity. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g)) :
    (Tx1Q_Carriers.prepared p).alpha=JFo_Prepared.value.alpha ∧
    (Tx1Q_Carriers.prepared p).rho=JFq_Rho.scalar ∧
    Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch=JFr_TX2_Powers.value ∧
    Tx1Q_Carriers.geometry g=JGp_Geometry.value () JGp_Seeds.geometry := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have powers := JHa_Powers.source p input scratch prepare
  have geometry := JGw_SameGeometry.source p g queries geo
  exact ⟨fields.2.2,rho.1,powers.2,geometry⟩
#print axioms source
end AspisR1.JHk_PowerInputs
end
