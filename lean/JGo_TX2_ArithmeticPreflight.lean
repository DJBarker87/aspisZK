import JGo_TX2_Cell0_0
import FIn_ExtractInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_ArithmeticPreflight
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def x : E := JGo_TX2_Cell0_0.value
def z : E := ⟨⟨⟨1572448860#u32,1407742788#u32⟩,⟨1176590543#u32,978776772#u32⟩⟩,
  ⟨⟨1659508991#u32,687669632#u32⟩,⟨1354109562#u32,1592313676#u32⟩⟩⟩
theorem addition : FIn_Primitives.add x x=ok z := by with_unfolding_all rfl
#print axioms addition
end AspisR1.JGo_TX2_ArithmeticPreflight
end
