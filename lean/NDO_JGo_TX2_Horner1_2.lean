import RPz7_FIn_ExtractInstall
import NDO_JGo_TX2_Cell1_4
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Horner1_2
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := ⟨⟨⟨1919636996#u32,850441629#u32⟩,⟨1054512366#u32,2047675035#u32⟩⟩,⟨⟨1522806534#u32,1392907138#u32⟩,⟨1343368380#u32,1056563952#u32⟩⟩⟩
def alpha : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def product : E := ⟨⟨⟨100559020#u32,2145473880#u32⟩,⟨678638851#u32,148771058#u32⟩⟩,⟨⟨2092385603#u32,1498312824#u32⟩,⟨284100823#u32,383052828#u32⟩⟩⟩
def after : E := ⟨⟨⟨2079094795#u32,439932571#u32⟩,⟨434540043#u32,1568675331#u32⟩⟩,⟨⟨658924286#u32,1836561602#u32⟩,⟨828011631#u32,893967187#u32⟩⟩⟩
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell1_4.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_Horner1_2
end
