-- Body retained from op208-opt-generated/Funs.lean. The still-opaque
-- compress256 symbol is an explicit parameter, not a new axiom or source law.
import R1Z.PV_CBL_ShaTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op208Extracted
open ProverRwFull
set_option autoImplicit false
abbrev Compression (base : ExternalTypes) :=
  Array U32 8#usize → PV_CBL_ShaTypes.Blocks base → Result (Array U32 8#usize)

def update_blocks (base : ExternalTypes) (compress : Compression base)
    (self : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) :
    Result PV_CBL_ShaCore.Core := do
  let i := Slice.len blocks
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (U64.wrapping_add self.block_len i1)
  let a ← compress self.state blocks
  ok { state := a, block_len := i2 }
#print axioms update_blocks
end R1Z.PV_CBL_Op208Extracted
