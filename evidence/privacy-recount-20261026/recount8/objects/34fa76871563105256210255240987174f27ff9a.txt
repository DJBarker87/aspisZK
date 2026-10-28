import R1Z.PhaseLocalityBin
import R0P.CircleSampler
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseCircleBlocksBin
def first (b : R0Z.FsStatement.OracleAnswer) :
    AspisR0.ChordGeometry.Point AspisWideTower.WideExact := by
  exact R0P.SemSource.circleSample0 (fun i => (b i).toFin)

def select (i : Fin 2) (b : R0Z.FsStatement.OracleAnswer) :
    AspisR0.ChordGeometry.Point AspisWideTower.WideExact := by
  by_cases hi : i.val = 0
  · exact first b
  · exact R0P.SemSource.circleSample1 (fun j => (b j).toFin)
#print axioms first
#print axioms select
end R1Z.PhaseCircleBlocksBin
