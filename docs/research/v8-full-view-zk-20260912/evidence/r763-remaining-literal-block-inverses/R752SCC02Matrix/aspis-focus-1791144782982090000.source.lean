/- Literal matrices from R724 certificate SCC 2; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC02Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 3) (Fin 3) M := ![
  ![(1073741772 : M), (1073741483 : M), (536870913 : M)],
  ![(2147483612 : M), (2147483409 : M), (0 : M)],
  ![(1073741826 : M), (1073741826 : M), (1073741772 : M)]
]

def B_scc : Matrix (Fin 3) (Fin 3) M := ![
  ![(1426302946 : M), (1026705530 : M), (806045168 : M)],
  ![(927152674 : M), (615972338 : M), (1523657323 : M)],
  ![(364437688 : M), (496728760 : M), (717723672 : M)]
]

end R752SCC02Matrix
