import Aeneas
import NNG_verify_finish.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option pp.explicit false
#print Aeneas.Std.core.cmp.PartialEq
#print Aeneas.Std.core.cmp.PartialEq.ne.default
#print Aeneas.Std.core.cmp.PartialEq.ne._default
example (c : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool) : (({ eq := c, ne := fun self other => core.cmp.PartialEq.ne.default c self other } : core.cmp.PartialEq aspis_core.field.QM31 aspis_core.field.QM31)) = { eq := c } := by
  rfl
