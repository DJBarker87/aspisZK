/- Literal matrices from R724 certificate SCC 18; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC18Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(42 : M), (1073743541 : M)],
  ![(5 : M), (7 : M)]
]

def B_scc : Matrix (Fin 2) (Fin 2) M := ![
  ![(859407756 : M), (511915979 : M)],
  ![(1226837586 : M), (861479242 : M)]
]

end R752SCC18Matrix
