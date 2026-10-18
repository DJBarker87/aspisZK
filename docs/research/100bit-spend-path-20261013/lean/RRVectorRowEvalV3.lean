import RRVectorRowBridgeV14
import Mathlib.Algebra.Field.ZMod
local instance : Fact (Nat.Prime 7) := ⟨by exact Nat.prime_seven⟩
#eval RRVectorRowBridge.row [[(1 : ZMod 7), 2], [3, 4]] (5 : ZMod 7) 1 2
#print axioms RRVectorRowBridge.row
