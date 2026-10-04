/- Literal matrices from R724 certificate SCC 31; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC31Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(1073741772 : M), (536870913 : M)],
  ![(1073741826 : M), (1073741772 : M)]
]

def B_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(315439843 : M), (914603284 : M)],
  ![(1829206568 : M), (315439843 : M)]
]

end R752SCC31Matrix
