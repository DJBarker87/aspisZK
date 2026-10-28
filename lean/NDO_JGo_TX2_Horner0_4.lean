import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell0_2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner0_4
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨1981950344#u32,1001337939#u32⟩,⟨56468361#u32,38371699#u32⟩⟩,⟨⟨1601463402#u32,1595103814#u32⟩,⟨1486308779#u32,565225692#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def product : E := ⟨⟨⟨737235730#u32,1824123850#u32⟩,⟨1909052753#u32,2132411430#u32⟩⟩,⟨⟨824022375#u32,621332507#u32⟩,⟨1851653134#u32,461731219#u32⟩⟩⟩
def after : E := ⟨⟨⟨758952064#u32,622204512#u32⟩,⟨1967989814#u32,1014082062#u32⟩⟩,⟨⟨1546522575#u32,60566906#u32⟩,⟨123002621#u32,719205769#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell0_2.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner0_4
end
