import Port5Q1_ListCells
set_option autoImplicit false
namespace AspisR1.Port5Q1_FiveCells
variable {F : Type} [Zero F]
theorem third (a b c d e : F) : [a,b,c,d,e][2]?.getD 0=c := by rfl
theorem fourth (a b c d e : F) : [a,b,c,d,e][3]?.getD 0=d := by rfl
theorem fifth (a b c d e : F) : [a,b,c,d,e][4]?.getD 0=e := by rfl
#print axioms third
#print axioms fourth
#print axioms fifth
end AspisR1.Port5Q1_FiveCells
