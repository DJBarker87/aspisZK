import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_1
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨457217806#u32,214550332#u32⟩,⟨1280429014#u32,1058658606#u32⟩⟩,⟨⟨1325225782#u32,697722630#u32⟩,⟨1125651937#u32,94446012#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨912108759#u32,1363509193#u32⟩,⟨473207639#u32,1392764201#u32⟩⟩,⟨⟨1614286045#u32,27813275#u32⟩,⟨1613020109#u32,981103400#u32⟩⟩⟩
def after : E := ⟨⟨⟨1919636996#u32,850441629#u32⟩,⟨1054512366#u32,2047675035#u32⟩⟩,⟨⟨1522806534#u32,1392907138#u32⟩,⟨1343368380#u32,1056563952#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_5.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_1
end
