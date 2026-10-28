import RPv_FJb_WideSum4
import RPu_FIq_Native01
set_option autoImplicit false
namespace AspisR1.JGj_ModulusWord
open Aeneas Aeneas.Std
theorem value : (FJb_WideSum4.wide FIq_Native.field.P).val=AspisV8R17.RawReducer.P := by
  rw [FJb_WideSum4.wide_val,FIq_Native.field.P]
  change 2147483647=AspisV8R17.RawReducer.P
  norm_num [AspisV8R17.RawReducer.P]
#print axioms value
end AspisR1.JGj_ModulusWord
