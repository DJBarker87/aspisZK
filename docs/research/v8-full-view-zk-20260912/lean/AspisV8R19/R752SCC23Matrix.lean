/- Literal matrices from R724 certificate SCC 23; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC23Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(42 : M), (245 : M)],
  ![(2147483612 : M), (2147483409 : M)]
]

def B_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(825141500 : M), (1481023205 : M)],
  ![(1015558769 : M), (359677064 : M)]
]

end R752SCC23Matrix
