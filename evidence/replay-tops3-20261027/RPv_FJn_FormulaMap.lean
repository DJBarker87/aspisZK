import RPv_FIr_TerminalValue
set_option autoImplicit false
namespace AspisR1.FJn_FormulaMap
variable {K L : Type} [Field K] [Field L]
def formula (eq comp mu h active : L) : L:=eq*comp+mu*h+mu^2*(1-active)*h
theorem value (f : K →+* L) (eq comp mu h active : K) :
    f (eq*comp+mu*h+mu^2*(1-active)*h)=formula (f eq) (f comp) (f mu) (f h) (f active) := by
  simp only [formula,map_add,map_mul,map_pow,map_sub,map_one]
#print axioms value
end AspisR1.FJn_FormulaMap
