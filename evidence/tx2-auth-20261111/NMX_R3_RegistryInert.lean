import NMX_R3_RegistryOps
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryInert
open Aeneas Aeneas.Std AdapterRw
/-- Explicit unused slots. Every reached scalar field is overwritten by the
CLOSED registry installation; native refinement is proved for every base. -/
def inert : Ops :=
 {
  op0 := by intros; exact .div,
  op1 := by intros; exact .div,
  op2 := by intros; exact .div,
  op3 := by intros; exact .div,
  op4 := by intros; exact .div,
  op5 := by intros; exact .div,
  op6 := by intros; exact .div,
  op7 := by intros; exact .div,
  op8 := by intros; exact .div,
  op9 := by intros; exact .div,
  op10 := by intros; exact .div,
  op11 := by intros; exact .div,
  op12 := by intros; exact .div,
  op13 := by intros; exact .div,
  op14 := by intros; exact .div,
  op15 := by intros; exact .div,
  op16 := by intros; exact .div,
  op17 := by intros; exact .div,
  op18 := by intros; exact .div,
  op19 := by intros; exact .div,
  op20 := by intros; exact .div,
  op21 := by intros; exact .div,
  op22 := by intros; exact .div,
  op23 := by intros; exact .div,
  op24 := by intros; exact .div,
  op25 := by intros; exact .div,
  op26 := by intros; exact .div,
  op27 := by intros; exact .div,
  op28 := by intros; exact .div,
  op29 := by intros; exact .div,
  op30 := by intros; exact .div,
  op31 := by intros; exact .div,
  op32 := by intros; exact .div,
  op33 := by intros; exact .div,
  op34 := by intros; exact .div,
  op35 := by intros; exact .div,
  op36 := by intros; exact .div,
  op37 := by intros; exact .div,
  op38 := by intros; exact .div,
  op39 := by intros; exact .div,
  op40 := by intros; exact .div,
  op41 := by intros; exact .div,
  op42 := by intros; exact .div,
  op43 := by intros; exact .div,
  op44 := by intros; exact .div,
  op45 := by intros; exact .div,
  op46 := by intros; exact .div,
  op47 := by intros; exact .div,
  op48 := by intros; exact .div,
  op49 := by intros; exact .div,
  op50 := by intros; exact .div,
  op51 := by intros; exact .div,
  op52 := by intros; exact .div,
  op53 := by intros; exact .div }

end NMX_R3_RegistryInert
end
