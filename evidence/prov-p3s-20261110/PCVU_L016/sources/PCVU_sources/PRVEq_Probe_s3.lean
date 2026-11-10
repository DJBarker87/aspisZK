-- PCVU_ probe 3: print the std definition used for the mutable slice iterator next (name test + definition text)
import Aeneas
import PRVEq_Tx2Deployed_s1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace PCVU_Probe3
set_option pp.proofs true
#print Aeneas.Std.core.slice.iter.IteratorIterMut.next
#check @Aeneas.Std.Slice.setAtNat
#print Aeneas.Std.Slice.setAtNat
end PCVU_Probe3
