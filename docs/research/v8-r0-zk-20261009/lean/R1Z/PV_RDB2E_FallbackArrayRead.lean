import R1Z.PV_RDB2D_SHAModel

section
-- Unchanged source component R1Z.PV_CBL_FallbackArrayRead
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackArrayRead
set_option autoImplicit false
theorem read {T : Type} [Inhabited T] {N : Usize} (v : Array T N) (i : Usize)
    (h : i.val<N.val) : Array.index_usize v i = ok v.val[i.val]! := by
  have hv : i.val<v.val.length := by simpa only [v.property] using h
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hv,Option.getD_some]
#print axioms read
end R1Z.PV_CBL_FallbackArrayRead

end
