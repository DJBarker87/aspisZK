/- Literal matrices from R724 certificate SCC 11; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC11Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(42 : M), (1073743541 : M), (0 : M), (536870913 : M)],
  ![(5 : M), (7 : M), (0 : M), (0 : M)],
  ![(0 : M), (1073741826 : M), (42 : M), (1073743541 : M)],
  ![(0 : M), (0 : M), (5 : M), (7 : M)]
]

def B_scc : Matrix (Fin 4) (Fin 4) M := ![
  ![(604448262 : M), (935588811 : M), (1742699959 : M), (2111692791 : M)],
  ![(795384754 : M), (1479205925 : M), (902697962 : M), (1866265166 : M)],
  ![(1337916271 : M), (2075901935 : M), (604448262 : M), (935588811 : M)],
  ![(1805395924 : M), (1585046685 : M), (795384754 : M), (1479205925 : M)]
]

end R752SCC11Matrix
