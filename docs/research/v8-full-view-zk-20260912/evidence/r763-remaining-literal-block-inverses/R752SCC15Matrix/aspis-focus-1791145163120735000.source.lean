/- Literal matrices from R724 certificate SCC 15; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC15Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(1073741772 : M), (1073741483 : M), (536870913 : M), (536870913 : M)],
  ![(2147483612 : M), (2147483409 : M), (0 : M), (0 : M)],
  ![(1073741826 : M), (1073741826 : M), (1073741772 : M), (1073741483 : M)],
  ![(0 : M), (0 : M), (2147483612 : M), (2147483409 : M)]
]

def B_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(1563663903 : M), (1106199413 : M), (1312621409 : M), (225882635 : M)],
  ![(970113817 : M), (2056991587 : M), (249096426 : M), (787878654 : M)],
  ![(477759171 : M), (451765270 : M), (1563663903 : M), (1106199413 : M)],
  ![(498192852 : M), (1575757308 : M), (970113817 : M), (2056991587 : M)]
]

end R752SCC15Matrix
