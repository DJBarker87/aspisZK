import NDO_JGw_InstalledSlots
import NDO_JGp_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_SameGeometry
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JGr_Geometry

theorem source (p : verifier.Prepared) (g : verifier.QueryGeometry)
    (queries : p.queries=JFq_Queries.value)
    (call : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g)) :
    Tx1Q_Carriers.geometry g=JGp_Geometry.value () JGp_Seeds.geometry := by
  rw [JGw_InstalledSlots.geometry] at call
  have native := Tx1Q_PrefixInstall.geometry_success
    (SAQ_Constructor.install () JGp_Seeds.geometry) p.queries 0#usize 10#usize g call
  rw [queries] at native
  have run : Port3_GeometryStage.geometry
      (Port5Q1_GeometryTerminal.install (SAQ_Constructor.install () JGp_Seeds.geometry))
      JFq_Queries.value 0#usize 10#usize=ok (.Ok (JGp_Geometry.value () JGp_Seeds.geometry)) :=
    JGp_Geometry.stage () JGp_Seeds.geometry
  exact core.result.Result.Ok.inj (Result.ok.inj (native.symm.trans run))
#print axioms source
end AspisR1.JGw_SameGeometry
end
