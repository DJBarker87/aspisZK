import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
@[global_simps, irreducible] def multiproof.BINARY_NODE_TAG : Std.U8 := 18#u8

/-- [aspis_r1_cost_probe::multiproof::sibling_binary_parent]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 78:0-81:1 -/
def multiproof.sibling_binary_parent
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (values : Array (Array Std.U8 32#usize) 16#usize)
  (index : Std.Usize) (sibling : Slice Std.U8) (left : Bool) :
  Result (Array Std.U8 32#usize)
  := do
  if left
  then
    let s ←
      lift (Array.to_slice (Array.make 1#usize [ multiproof.BINARY_NODE_TAG ]))
    let a ← Array.index_usize values index
    let s1 ← lift (Array.to_slice a)
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, sibling ]))
    aspis_coredigestDigest32Inst.digest hash s2
  else
    let s ←
      lift (Array.to_slice (Array.make 1#usize [ multiproof.BINARY_NODE_TAG ]))
    let a ← Array.index_usize values index
    let s1 ← lift (Array.to_slice a)
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, sibling, s1 ]))
    aspis_coredigestDigest32Inst.digest hash s2

/-- [aspis_r1_cost_probe::multiproof::occupied_binary_parent]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 73:0-75:1 -/
def multiproof.occupied_binary_parent
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (values : Array (Array Std.U8 32#usize) 16#usize)
  (index : Std.Usize) :
  Result (Array Std.U8 32#usize)
  := do
  let s ←
    lift (Array.to_slice (Array.make 1#usize [ multiproof.BINARY_NODE_TAG ]))
  let a ← Array.index_usize values index
  let s1 ← lift (Array.to_slice a)
  let i ← index + 1#usize
  let a1 ← Array.index_usize values i
  let s2 ← lift (Array.to_slice a1)
  let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
  aspis_coredigestDigest32Inst.digest hash s3


end AspisR1Stage2
