import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_5
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨665706578#u32,662812829#u32⟩,⟨1242603235#u32,110573225#u32⟩⟩,⟨⟨1907829652#u32,1975329920#u32⟩,⟨403417240#u32,1407134899#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨1523903392#u32,1615309050#u32⟩,⟨191706735#u32,1365325123#u32⟩⟩,⟨⟨1211671404#u32,74839695#u32⟩,⟨522744072#u32,2094526260#u32⟩⟩⟩
def after : E := ⟨⟨⟨1407090889#u32,2014466468#u32⟩,⟨358752975#u32,194707736#u32⟩⟩,⟨⟨133772631#u32,93019705#u32⟩,⟨125829515#u32,658546135#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_1.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_5
end
