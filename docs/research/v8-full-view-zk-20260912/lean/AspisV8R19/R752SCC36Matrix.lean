/- Literal matrices from R724 certificate SCC 36; generated without recomputing products. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace R752SCC36Matrix
abbrev M := ZMod 2147483647

def A_scc : Matrix (Fin 3) (Fin 3) M := ![
  ![(42 : M), (1073743541 : M), (245 : M)],
  ![(5 : M), (7 : M), (2147483642 : M)],
  ![(0 : M), (1073741826 : M), (0 : M)]
]

def B_scc : Matrix (Fin 3) (Fin 3) M := ![
  ![(411538678 : M), (838042399 : M), (1830224736 : M)],
  ![(0 : M), (0 : M), (1717986918 : M)],
  ![(411538678 : M), (2126532587 : M), (799432586 : M)]
]

end R752SCC36Matrix
