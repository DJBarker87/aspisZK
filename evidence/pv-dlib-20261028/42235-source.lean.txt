-- Exact two-field carrier retained from op208-opt-generated/Types.lean.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_ShaCore
structure Core where
  state : Array U32 8#usize
  block_len : U64
#print axioms Core
end PV_CBL_ShaCore
