import JGr_BatchInputs
import JGw_GeometryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_QueryReads
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) (i : Fin 10) :
    Array.index_usize p.queries (JGw_GeometryReads.cursor i)=ok (JGp_Rows.query i) := by
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  rw [queries]
  fin_cases i <;> rfl
#print axioms source
end AspisR1.JGw_QueryReads
end
