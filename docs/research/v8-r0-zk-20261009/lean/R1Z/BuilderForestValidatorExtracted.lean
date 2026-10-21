-- Dependency slice of the part-9 generated validator; see the port receipt.
import R1Z.BuilderForestStdPort
import R1Z.BuilderStdShift
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace AspisBuilderForestValidator
@[reducible]
def aspis_core.field.M31 := Std.U32

def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

impl_def aspis_core.field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq
  aspis_core.field.M31 aspis_core.field.M31 := {
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31
}

structure pool_v1.incremental_merkle.IncrementalMerkleTreeV1 where
  next_leaf_index : Std.U64
  root : Array aspis_core.field.M31 8#usize
  frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize

inductive pool_v1.incremental_merkle.PoolV1TreeError where
| TreeFull : pool_v1.incremental_merkle.PoolV1TreeError
| InsufficientCapacity : pool_v1.incremental_merkle.PoolV1TreeError
| IndexOutOfRange : pool_v1.incremental_merkle.PoolV1TreeError
| RootMismatch : pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalFrontier : pool_v1.incremental_merkle.PoolV1TreeError
| WrongLength : pool_v1.incremental_merkle.PoolV1TreeError
| WrongMagic : pool_v1.incremental_merkle.PoolV1TreeError
| WrongVersion : pool_v1.incremental_merkle.PoolV1TreeError
| WrongDepth : pool_v1.incremental_merkle.PoolV1TreeError
| WrongTreeHash : pool_v1.incremental_merkle.PoolV1TreeError
| WrongDigestEncoding : pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalDigest : pool_v1.incremental_merkle.PoolV1TreeError
| NonZeroReserved : pool_v1.incremental_merkle.PoolV1TreeError

def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

def pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : Result Std.U64 :=
  1#u64 <<< 20#u32

def pool_v1.incremental_merkle.tree_reference.validate_owned_loop
  (i : Std.U64) (a : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (empty : Array (Array aspis_core.field.M31 8#usize) 21#usize)
  (result : core.result.Result Unit pool_v1.incremental_merkle.PoolV1TreeError)
  (level : Std.Usize) :
  Result (core.result.Result Unit pool_v1.incremental_merkle.PoolV1TreeError)
  := do
  if level < pool_v1.format.POOL_V1_TREE_DEPTH
  then
    let b ← core.result.Result.is_ok result
    if b
    then
      let i1 ← lift (R1Z.BuilderStdModels.shift64 i level)
      let i2 ← lift (i1 &&& 1#u64)
      let result1 ←
        if i2 = 0#u64
        then
          do
          let a1 ← Array.index_usize a level
          let a2 ← Array.index_usize empty level
          let b1 ←
            core.array.equality.PartialEqArray.ne
              aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a1 a2
          if b1
          then
            ok (core.result.Result.Err
              pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier)
          else ok result
        else ok result
      let level1 ← lift (Std.Usize.wrapping_add level 1#usize)
      pool_v1.incremental_merkle.tree_reference.validate_owned_loop i a empty
        result1 level1
    else ok result
  else ok result
partial_fixpoint

def pool_v1.incremental_merkle.tree_reference.validate_owned
  (reconstruct : pool_v1.incremental_merkle.IncrementalMerkleTreeV1 →
    Array (Array aspis_core.field.M31 8#usize) 21#usize →
    Result (core.result.Result (Array aspis_core.field.M31 8#usize)
      pool_v1.incremental_merkle.PoolV1TreeError))
  (tree : pool_v1.incremental_merkle.IncrementalMerkleTreeV1)
  (empty : Array (Array aspis_core.field.M31 8#usize) 21#usize) :
  Result (core.result.Result Unit pool_v1.incremental_merkle.PoolV1TreeError)
  := do
  let i ← pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
  if tree.next_leaf_index > i
  then
    ok (core.result.Result.Err
      pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange)
  else
    let result ←
      pool_v1.incremental_merkle.tree_reference.validate_owned_loop
        tree.next_leaf_index tree.frontier empty (core.result.Result.Ok ())
        0#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch result
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      if tree.next_leaf_index = 0#u64
      then
        let a ← Array.index_usize empty pool_v1.format.POOL_V1_TREE_DEPTH
        let b ←
          core.array.equality.PartialEqArray.eq
            aspis_core.field.M31.Insts.CoreCmpPartialEqM31 tree.root a
        if b
        then ok (core.result.Result.Ok ())
        else
          ok (core.result.Result.Err
            pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch)
      else
        if tree.next_leaf_index < i
        then
          let r ←
            reconstruct tree empty
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue val =>
            let b ←
              core.array.equality.PartialEqArray.ne
                aspis_core.field.M31.Insts.CoreCmpPartialEqM31 val tree.root
            if b
            then
              ok (core.result.Result.Err
                pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch)
            else ok (core.result.Result.Ok ())
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              pool_v1.incremental_merkle.PoolV1TreeError) residual
        else ok (core.result.Result.Ok ())
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame pool_v1.incremental_merkle.PoolV1TreeError)
        residual


#print axioms pool_v1.incremental_merkle.tree_reference.validate_owned_loop
#print axioms pool_v1.incremental_merkle.tree_reference.validate_owned
end AspisBuilderForestValidator
