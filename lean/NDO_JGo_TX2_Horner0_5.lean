import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_5
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨758952064#u32,622204512#u32⟩,⟨1967989814#u32,1014082062#u32⟩⟩,⟨⟨1546522575#u32,60566906#u32⟩,⟨123002621#u32,719205769#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨1135573705#u32,106601683#u32⟩,⟨1561817237#u32,1976630472#u32⟩⟩,⟨⟨2035191667#u32,1443016463#u32⟩,⟨758064976#u32,1840850243#u32⟩⟩⟩
def after : E := ⟨⟨⟨1292966132#u32,1083154571#u32⟩,⟨784644818#u32,1742081190#u32⟩⟩,⟨⟨2041950274#u32,93975283#u32⟩,⟨817782919#u32,460812233#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_1.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_5
end
