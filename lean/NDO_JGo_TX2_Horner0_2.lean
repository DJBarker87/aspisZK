import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_4
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_2
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨738223870#u32,1866538469#u32⟩,⟨1246977601#u32,537786410#u32⟩⟩,⟨⟨1336898523#u32,1155119503#u32⟩,⟨1008163169#u32,627628314#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨301965535#u32,2061211146#u32⟩,⟨1582238600#u32,1931192300#u32⟩⟩,⟨⟨1912862096#u32,2016560155#u32⟩,⟨1627037116#u32,2034488491#u32⟩⟩⟩
def after : E := ⟨⟨⟨2076632800#u32,563408347#u32⟩,⟨1906917041#u32,1746014407#u32⟩⟩,⟨⟨1583292743#u32,470178804#u32⟩,⟨1876434637#u32,485398198#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_4.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_2
end
