/- Generated from the source-pinned T163 table, verified against the source constructor. -/
import AspisV8R19.ResidualModel
namespace AspisR19.ResidualPins
def order : Fin 111 → Nat := fun i => [13,14,15,29,30,31,45,46,47,61,62,63,77,78,79,93,94,95,109,110,111,125,126,127,141,142,143,157,158,159,173,174,175,189,190,191,205,206,207,221,222,223,237,238,239,253,254,255,269,270,271,285,286,287,301,302,303,317,318,319,333,334,335,349,350,351,365,366,367,381,382,383,397,398,399,413,414,415,429,430,431,445,446,447,461,462,463,477,478,89,90,91,92,0,1,2,96,97,98,99,100,101,102,103,104,105,106,107,108,3,4].getD i.val 0
def inactive : Fin 111 → Bool := fun i => [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,false,true,true].getD i.val false
theorem order_bounds : ∀ i, order i<1023 := by decide
#print axioms order_bounds
end AspisR19.ResidualPins
