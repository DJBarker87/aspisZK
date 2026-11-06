import NJA_Matrix

set_option autoImplicit false
namespace NJE_ConstantsInternal
open Aeneas Aeneas.Std
abbrev K := NJA_Matrix.K

def source : Fin 14 → U32 :=
  ![2139014335#u32,69309039#u32,1368974953#u32,886780232#u32,1130937085#u32,1718115455#u32,2027103386#u32,1612216449#u32,1994053242#u32,110146615#u32,514413329#u32,1088763546#u32,955319292#u32,488794657#u32]

theorem canonical (r : Fin 14) : (source r).val<2147483647 := by
 fin_cases r <;> norm_num [source]

theorem model (r : Fin 14) : ((source r).val:K)=R0P.poseidonInternalConstants r := by
 fin_cases r <;> rfl

#print canonical
#print axioms canonical
#print model
#print axioms model
end NJE_ConstantsInternal
