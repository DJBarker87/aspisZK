import Aeneas
set_option autoImplicit false
namespace NMX_R3_RawWord64Defs
def encoded (v : Fin 8 → BitVec 8) : BitVec 64 := BitVec.fromLEBytes [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]
def folded (v : Fin 8 → BitVec 8) : BitVec 64 :=
 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7].foldr (fun x acc => (acc <<< 8) ||| x.setWidth 64) 0
end NMX_R3_RawWord64Defs
