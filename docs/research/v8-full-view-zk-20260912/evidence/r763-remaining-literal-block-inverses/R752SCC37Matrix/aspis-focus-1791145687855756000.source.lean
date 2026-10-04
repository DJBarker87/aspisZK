/- Literal matrices from R724 certificate SCC 37; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC37Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(1073741772 : M), (2147481246 : M), (536870913 : M), (0 : M)],
  ![(5 : M), (7 : M), (0 : M), (0 : M)],
  ![(0 : M), (1073741826 : M), (42 : M), (1073743541 : M)],
  ![(0 : M), (0 : M), (5 : M), (7 : M)]
]

def B_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(1995556698 : M), (1656377896 : M), (204852091 : M), (1431075461 : M)],
  ![(1642436140 : M), (1884706713 : M), (160460456 : M), (818503511 : M)],
  ![(320920912 : M), (1587498476 : M), (972253925 : M), (1201764849 : M)],
  ![(1611471046 : M), (706772786 : M), (2066583314 : M), (61946671 : M)]
]

end R752SCC37Matrix
