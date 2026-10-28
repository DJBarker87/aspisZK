import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_4
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨430518333#u32,614925926#u32⟩,⟨80332094#u32,1981595464#u32⟩⟩,⟨⟨962138503#u32,691657432#u32⟩,⟨205400575#u32,1015925020#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨1285810679#u32,982311169#u32⟩,⟨770827146#u32,1432423928#u32⟩⟩,⟨⟨2016269477#u32,1881792026#u32⟩,⟨674011535#u32,108495429#u32⟩⟩⟩
def after : E := ⟨⟨⟨665706578#u32,662812829#u32⟩,⟨1242603235#u32,110573225#u32⟩⟩,⟨⟨1907829652#u32,1975329920#u32⟩,⟨403417240#u32,1407134899#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_2.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_4
end
