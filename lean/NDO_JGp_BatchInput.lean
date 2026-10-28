import NDO_JGp_CurrentRoots
import NDO_JGp_TX1Geometry
set_option autoImplicit false
namespace AspisR1.JGp_BatchInput
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition

theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (err : C) (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (folded : Array U8 32#usize)
    (success : verifier.candidate.prepare (JGp_TX1Geometry.ops base query err geo)
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    (JGp_TX1Geometry.ops base query err geo).op6
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) JFx_NativeBytes.proof p folded 0#usize hash=
      Op5T_Install.mapResult Op5T_Install.currentError
        (Op5T_Install.body Port4B_Install.leaves
          (⟨D.coremarkerCopyInst,(F3V_OracleDictionary.current JFp_SHADigest.digest D).digest⟩ : AspisR1Stage2.aspis_core.digest.Digest32 H)
          JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots folded 0#usize hash) := by
  have queries := JGp_CurrentQueries.source _ _ _ D hash p input scratch success
  have roots := JGp_CurrentRoots.source _ _ _ D hash p input scratch success
  change Op5T_Install.mapResult Op5T_Install.currentError
    (Op5T_Install.body Port4B_Install.leaves _ JFx_NativeBytes.proof p.queries p.roots folded 0#usize hash)=_
  rw [queries,roots]
  rfl
#print axioms source
#print Tx1Reachability.afterPrepare
end AspisR1.JGp_BatchInput
