import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_6
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨1292966132#u32,1083154571#u32⟩,⟨784644818#u32,1742081190#u32⟩⟩,⟨⟨2041950274#u32,93975283#u32⟩,⟨817782919#u32,460812233#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨1293298497#u32,1267199240#u32⟩,⟨1672933553#u32,927287132#u32⟩⟩,⟨⟨1607446231#u32,622055518#u32⟩,⟨1841101059#u32,901260356#u32⟩⟩⟩
def after : E := ⟨⟨⟨2079522927#u32,1971070634#u32⟩,⟨1187487001#u32,1416675518#u32⟩⟩,⟨⟨1363458903#u32,965890334#u32⟩,⟨370672193#u32,1697417194#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_0.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_6
end
