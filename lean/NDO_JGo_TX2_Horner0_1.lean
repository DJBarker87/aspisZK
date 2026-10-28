import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_1
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨584569252#u32,399463886#u32⟩,⟨642592661#u32,182188033#u32⟩⟩,⟨⟨2121029331#u32,829695140#u32⟩,⟨468000119#u32,2030690898#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨1442116360#u32,761106798#u32⟩,⟨281800674#u32,104693594#u32⟩⟩,⟨⟨1303682888#u32,1847577401#u32⟩,⟨1067166816#u32,696113396#u32⟩⟩⟩
def after : E := ⟨⟨⟨738223870#u32,1866538469#u32⟩,⟨1246977601#u32,537786410#u32⟩⟩,⟨⟨1336898523#u32,1155119503#u32⟩,⟨1008163169#u32,627628314#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_5.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_1
end
