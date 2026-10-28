import NDO_JGp_CurrentQueries
import NDO_JGp_TX1Initial
import NDO_JGp_Geometry
import SAQ_Decoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_TX1Geometry
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition

def ops {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (err : C) (geo : Port3_NativeGeometryBody.Ops C) : Ops :=
  JGp_PrepareLayout.installed (JGp_Allocation.base (Op5T_Concrete.current base))
    (SAQ_Decoder.install query) (SAQ_Constructor.install err geo)

theorem inhabited {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (err : C) (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H) :
    let installed := ops base query err geo
    let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof hash none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ installed.op20 .S2=ok (.Ok initial) ∧
      installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      verifier.candidate.tx1 installed D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize hash none=
        Tx1Reachability.afterPrepare installed D0 JFx_NativeBytes.publicInput JFx_NativeBytes.proof
          10#usize hash none p scratch := by
  dsimp only
  obtain ⟨p,scratch,initial,pending,prepare,init,pend,entry⟩ :=
    JGp_TX1Initial.inhabited (Op5T_Concrete.current base) (SAQ_Decoder.install query)
      (SAQ_Constructor.install err geo) D hash
  have identified := JGp_CurrentQueries.source _ _ _ D hash p _ scratch prepare
  let g := Tx1Q_PrefixInstall.unGeometry (JGp_Geometry.value err geo)
  have geometry : (ops base query err geo).op19 p.queries 0#usize 10#usize=ok (.Ok g) := by
    change Tx1Q_PrefixInstall.geometryBody (SAQ_Constructor.install err geo) p.queries 0#usize 10#usize=_
    unfold Tx1Q_PrefixInstall.geometryBody Tx1Q_PrefixInstall.topResult
    rw [identified]
    have geometric : Port3_GeometryStage.geometry
        (Port5Q1_GeometryTerminal.install (SAQ_Constructor.install err geo))
        JFq_Queries.value 0#usize 10#usize=ok (.Ok (JGp_Geometry.value err geo)) := JGp_Geometry.stage err geo
    erw [geometric,bind_tc_ok]
  refine ⟨p,scratch,initial,pending,g,prepare,identified,init,pend,geometry,?_,entry⟩
  exact JGp_Geometry.meaning err geo
#print axioms inhabited
end AspisR1.JGp_TX1Geometry
end
