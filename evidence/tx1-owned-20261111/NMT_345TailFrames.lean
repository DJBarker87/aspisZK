import NMT_345Raw_11
import NMT_345Raw_12
import NMT_345Semantic
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std
structure HasPrefix (W : Type) extends Bounds W where
 proofPrefix : Slice U8
structure PrefixReply (W : Type) extends HasPrefix W where
 prefixMismatch : Bool
structure TagOffset (W : Type) extends PrefixReply W where
 tagOffset : Usize
structure TagByte (W : Type) extends TagOffset W where
 tagByte : U8
structure TagExpected (W : Type) extends TagByte W where
 expectedTag : U8
structure HasPublic (W : Type) extends TagExpected W where
 semanticPublic : Public
structure HasProofSlice (W : Type) extends HasPublic W where
 proofSlice : Slice U8
structure HasSplitByte (W : Type) extends HasProofSlice W where
 splitByte : U8
structure HasSplit (W : Type) extends HasSplitByte W where
 split : Usize
end NMT_345
