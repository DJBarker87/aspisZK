import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_3
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨2079094795#u32,439932571#u32⟩,⟨434540043#u32,1568675331#u32⟩⟩,⟨⟨658924286#u32,1836561602#u32⟩,⟨828011631#u32,893967187#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨586255668#u32,1082281758#u32⟩,⟨1860683536#u32,1339459494#u32⟩⟩,⟨⟨637604215#u32,1035442184#u32⟩,⟨292014533#u32,1856597523#u32⟩⟩⟩
def after : E := ⟨⟨⟨430518333#u32,614925926#u32⟩,⟨80332094#u32,1981595464#u32⟩⟩,⟨⟨962138503#u32,691657432#u32⟩,⟨205400575#u32,1015925020#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_3.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_3
end
