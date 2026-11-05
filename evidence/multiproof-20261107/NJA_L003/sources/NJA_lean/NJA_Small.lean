import NJA_Multiproof.Types
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace NJA_Multiproof

@[global_simps, irreducible] def multiproof.LEAF_BITS : Std.U32 := 18#u32


@[global_simps, irreducible] def multiproof.BINARY_NODE_TAG : Std.U8 := 18#u8


@[global_simps, irreducible] def multiproof.MAX_BATCH : Std.Usize := 16#usize


def multiproof.Arity.bits (self : multiproof.Arity) : Result Std.U32 := do
  match self with
  | multiproof.Arity.Two => ok 1#u32
  | multiproof.Arity.Eight => ok 3#u32


def multiproof.Arity.width (self : multiproof.Arity) : Result Std.Usize := do
  let i ← multiproof.Arity.bits self
  ok (Std.Usize.wrapping_shl 1#usize i)


def multiproof.Arity.levels (self : multiproof.Arity) : Result Std.U32 := do
  let i ← multiproof.Arity.bits self
  multiproof.LEAF_BITS / i


def multiproof.index_at
  (indices : Array Std.U32 16#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize indices index


def multiproof.value_at
  (values : Array (Array Std.U8 32#usize) 16#usize) (index : Std.Usize) :
  Result (Array Std.U8 32#usize)
  := do
  Array.index_usize values index


def multiproof.root_matches
  (values : Array (Array Std.U8 32#usize) 16#usize)
  (root : Array Std.U8 32#usize) :
  Result Bool
  := do
  let a ← Array.index_usize values 0#usize
  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a root


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
  let i ← lift (Std.Usize.wrapping_add index 1#usize)
  let a1 ← Array.index_usize values i
  let s2 ← lift (Array.to_slice a1)
  let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
  aspis_coredigestDigest32Inst.digest hash s3


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

end NJA_Multiproof
