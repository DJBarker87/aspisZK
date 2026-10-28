import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_6
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨1407090889#u32,2014466468#u32⟩,⟨358752975#u32,194707736#u32⟩⟩,⟨⟨133772631#u32,93019705#u32⟩,⟨125829515#u32,658546135#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨1105081449#u32,408904490#u32⟩,⟨1852829607#u32,1958652003#u32⟩⟩,⟨⟨1193201135#u32,1064240846#u32⟩,⟨2043047379#u32,105685028#u32⟩⟩⟩
def after : E := ⟨⟨⟨1257039141#u32,1533471634#u32⟩,⟨783187430#u32,1966658433#u32⟩⟩,⟨⟨283172619#u32,2041206475#u32⟩,⟨2128675531#u32,1092866791#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_0.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_6
end
