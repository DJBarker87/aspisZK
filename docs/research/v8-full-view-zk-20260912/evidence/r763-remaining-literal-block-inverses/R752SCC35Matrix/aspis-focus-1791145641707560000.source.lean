/- Literal matrices from R724 certificate SCC 35; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC35Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(1073741772 : M), (1073741483 : M)],
  ![(2147483612 : M), (2147483409 : M)]
]

def B_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(221390066 : M), (901373844 : M)],
  ![(1483313447 : M), (1897629143 : M)]
]

end R752SCC35Matrix
