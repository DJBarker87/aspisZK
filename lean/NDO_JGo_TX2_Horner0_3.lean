import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_3
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨2076632800#u32,563408347#u32⟩,⟨1906917041#u32,1746014407#u32⟩⟩,⟨⟨1583292743#u32,470178804#u32⟩,⟨1876434637#u32,485398198#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨1679165634#u32,426448666#u32⟩,⟨1344705716#u32,492480991#u32⟩⟩,⟨⟨1743285394#u32,566604073#u32⟩,⟨104532738#u32,192380230#u32⟩⟩⟩
def after : E := ⟨⟨⟨1981950344#u32,1001337939#u32⟩,⟨56468361#u32,38371699#u32⟩⟩,⟨⟨1601463402#u32,1595103814#u32⟩,⟨1486308779#u32,565225692#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_3.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_3
end
