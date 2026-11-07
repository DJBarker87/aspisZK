import NMT_345Raw_10
import NMT_345Raw_11
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std
structure HasLength (W : Type) extends ProofData W where
 proofLength : Usize
structure HasStart (W : Type) extends HasLength W where
 proofStart : Usize
structure HasSum (W : Type) extends HasStart W where
 checkedSum : Option Usize
end NMT_345
