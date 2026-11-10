-- NPL_PublicBytesRef.lean (Stream A job NPL_, 2026-11-10)
--
-- CLASS: ReviewedTranscription. This file is a HAND transcription, not an Aeneas emission.
-- It is evidence only to the extent that a reviewer accepts the line-by-line correspondence
-- recorded in the comments below against the frozen Rust text quoted in NPL_PUBLIC_BYTES.md.
--
-- Frozen source (revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387):
--   crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs
--     (file sha256 4e209947ac75532af1c7d79f339050aab6b57379fc3962e1df9ff5602087787e)
--     public_bytes        lines 2017-2077 (sha256 of those lines 46feab6146ac57be857df3082aaa7258cb870dcf5c2ba90883b453574138a312)
--     Public::semantic    lines 2005-2010
--     private_public      lines 1327-1343
--     withdrawal_public   lines 1345-1361
--   crates/aspis-core/src/field.rs line 19: pub const P: u32 = 0x7fff_ffff;
--
-- Carriers: the transcription reuses the carrier TYPES of the gate module
-- (AspisR1PublicPreparation.Types; it does NOT import AspisR1PublicPreparation.Funs, so no gate
-- function or constant is referenced here). Carrier conventions, each a reviewed item:
--   * Rust `M31(pub u32)` is the gate's `aspis_core.field.M31 := Std.U32`, so `value.0` is `value`
--     and `M31(value)` is `value`.
--   * Rust `Digest = [M31; 8]` is `Array aspis_core.field.M31 8#usize`; `[Digest; 20]` is
--     `Array (Array aspis_core.field.M31 8#usize) 20#usize` (POOL_V1_PAIR_TREE_DEPTH = 20).
--   * Rust references `&'a T` are values; `&mut Vec<u8>` is threaded and returned (Aeneas convention),
--     on the error path too.
--   * Rust `Result<T, Error>` is `core.result.Result T aspis_core.state_only_prefix.r0.Error` inside the Aeneas `Result` monad;
--     Aeneas `fail` models a Rust panic (here only Vec capacity overflow).
--   * Rust `e?` is Aeneas' `Try::branch` / `FromResidual::from_residual` pair (helpers `tryUnit`,
--     `tryTop`), the same library functions Aeneas emits for `?`.
--   * Rust `for value in values` is `IntoIterator::into_iter` on the slice, then `loop` over
--     `Iterator::next` (Aeneas library models).
import Aeneas
import AspisR1PublicPreparation.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace NPL_PublicBytesRef
open AspisR1PublicPreparation

/-- crates/aspis-core/src/field.rs:19 `pub const P: u32 = 0x7fff_ffff;` (0x7fff_ffff = 2147483647). -/
def P : Std.U32 := 2147483647#u32

/-- frozen 1327-1343 `fn private_public(public, transition) -> SemanticPublic`:
    one struct literal, field by field in source order. -/
def private_public
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer, -- 1332
      pool := public1.pool,                                                             -- 1333
      deployment_domain := public1.deployment_domain,                                   -- 1334
      anchor := public1.anchor_root,                                                    -- 1335
      nullifier := public1.nullifier,                                                   -- 1336
      asset_id := public1.asset_id,                                                     -- 1337
      recipient := (some public1.recipient_commitment),                                 -- 1338
      change := public1.change_commitment,                                              -- 1339
      withdrawal_amount := none,                                                        -- 1340
      transition                                                                        -- 1341
    }

/-- frozen 1345-1361 `fn withdrawal_public(public, transition) -> SemanticPublic`. -/
def withdrawal_public
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal,      -- 1350
      pool := public1.pool,                                                             -- 1351
      deployment_domain := public1.deployment_domain,                                   -- 1352
      anchor := public1.anchor_root,                                                    -- 1353
      nullifier := public1.nullifier,                                                   -- 1354
      asset_id := public1.asset_id,                                                     -- 1355
      recipient := none,                                                                -- 1356
      change := public1.change_commitment,                                              -- 1357
      withdrawal_amount := (some public1.amount),                                       -- 1358
      transition                                                                        -- 1359
    }

/-- frozen 2005-2010 `fn semantic(self) -> SemanticPublic { match self { .. } }`. -/
def semantic
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer public1 transition =>     -- 2007
    private_public public1 transition
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal public1 transition =>   -- 2008
    withdrawal_public public1 transition

/-- frozen 2019-2024, one iteration of `for value in values { .. }` inside `fn fields`. -/
def fields_loop.body
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.M31) ×
    (alloc.vec.Vec Std.U8)) ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter        -- 2019 for value in values
  match o with
  | none => ok (done (core.result.Result.Ok (), out))                  -- 2024 loop ends; 2025 Ok(())
  | some value =>
    if value >= P                                                      -- 2020 if value.0 >= P
    then
      ok (done (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public, out))             -- 2021 return Err(Error::Public)
    else
      let a ← lift (core.num.U32.to_le_bytes value)                    -- 2023 value.0.to_le_bytes()
      let s ← lift (Array.to_slice a)                                  -- 2023 &[u8; 4] as &[u8]
      let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s  -- 2023 out.extend_from_slice
      ok (cont (iter1, out1))

/-- frozen 2019-2024 the loop itself. -/
def fields_loop
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))
  := do
  loop (fun (iter1, out1) => NPL_PublicBytesRef.fields_loop.body iter1 out1) (iter, out)

/-- frozen 2018-2026 `fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error>`. -/
def fields
  (out : alloc.vec.Vec Std.U8) (values : Slice aspis_core.field.M31) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))
  := do
  let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values  -- 2019
  fields_loop iter out

/-- Rust `e?;` inside a helper returning `Result<(), Error>` that holds `out: &mut Vec<u8>`:
    on `Ok` continue with `k`; on `Err` return the converted residual and the current `out`. -/
def tryUnit
  (x : Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
  (k : alloc.vec.Vec Std.U8 → Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))
  := do
  let (r, out1) ← x
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => k out1
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual
    ok (r1, out1)

/-- Rust `e?;` inside `public_bytes` (returns `Result<Vec<u8>, Error>`; the local `out` is dropped
    on the error path). -/
def tryTop
  (x : Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
  (k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)
  := do
  let (r, out1) ← x
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => k out1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual

/-- Rust `if let Some(value) = o { fields(&mut out, <slice of value>)?; }` followed by the rest `k`. -/
def ifSomeFields {α : Type}
  (o : Option α) (out : alloc.vec.Vec Std.U8) (slice : α → Slice aspis_core.field.M31)
  (k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)
  :=
  match o with
  | none => k out
  | some value => do
    let s ← lift (slice value)
    tryTop (fields out s) k

/-- frozen 2029-2051 `fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error>`:
    twenty explicit calls, as in the source. -/
def frontier
  (out : alloc.vec.Vec Std.U8)
  (values : Array (Array aspis_core.field.M31 8#usize) 20#usize) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))
  := do
  -- frozen line 2030: fields(out, &values[0])?;
  let a ← Array.index_usize values 0#usize
  let s ← lift (Array.to_slice a)
  tryUnit (fields out s) fun out => do
    -- frozen line 2031: fields(out, &values[1])?;
    let a ← Array.index_usize values 1#usize
    let s ← lift (Array.to_slice a)
    tryUnit (fields out s) fun out => do
      -- frozen line 2032: fields(out, &values[2])?;
      let a ← Array.index_usize values 2#usize
      let s ← lift (Array.to_slice a)
      tryUnit (fields out s) fun out => do
        -- frozen line 2033: fields(out, &values[3])?;
        let a ← Array.index_usize values 3#usize
        let s ← lift (Array.to_slice a)
        tryUnit (fields out s) fun out => do
          -- frozen line 2034: fields(out, &values[4])?;
          let a ← Array.index_usize values 4#usize
          let s ← lift (Array.to_slice a)
          tryUnit (fields out s) fun out => do
            -- frozen line 2035: fields(out, &values[5])?;
            let a ← Array.index_usize values 5#usize
            let s ← lift (Array.to_slice a)
            tryUnit (fields out s) fun out => do
              -- frozen line 2036: fields(out, &values[6])?;
              let a ← Array.index_usize values 6#usize
              let s ← lift (Array.to_slice a)
              tryUnit (fields out s) fun out => do
                -- frozen line 2037: fields(out, &values[7])?;
                let a ← Array.index_usize values 7#usize
                let s ← lift (Array.to_slice a)
                tryUnit (fields out s) fun out => do
                  -- frozen line 2038: fields(out, &values[8])?;
                  let a ← Array.index_usize values 8#usize
                  let s ← lift (Array.to_slice a)
                  tryUnit (fields out s) fun out => do
                    -- frozen line 2039: fields(out, &values[9])?;
                    let a ← Array.index_usize values 9#usize
                    let s ← lift (Array.to_slice a)
                    tryUnit (fields out s) fun out => do
                      -- frozen line 2040: fields(out, &values[10])?;
                      let a ← Array.index_usize values 10#usize
                      let s ← lift (Array.to_slice a)
                      tryUnit (fields out s) fun out => do
                        -- frozen line 2041: fields(out, &values[11])?;
                        let a ← Array.index_usize values 11#usize
                        let s ← lift (Array.to_slice a)
                        tryUnit (fields out s) fun out => do
                          -- frozen line 2042: fields(out, &values[12])?;
                          let a ← Array.index_usize values 12#usize
                          let s ← lift (Array.to_slice a)
                          tryUnit (fields out s) fun out => do
                            -- frozen line 2043: fields(out, &values[13])?;
                            let a ← Array.index_usize values 13#usize
                            let s ← lift (Array.to_slice a)
                            tryUnit (fields out s) fun out => do
                              -- frozen line 2044: fields(out, &values[14])?;
                              let a ← Array.index_usize values 14#usize
                              let s ← lift (Array.to_slice a)
                              tryUnit (fields out s) fun out => do
                                -- frozen line 2045: fields(out, &values[15])?;
                                let a ← Array.index_usize values 15#usize
                                let s ← lift (Array.to_slice a)
                                tryUnit (fields out s) fun out => do
                                  -- frozen line 2046: fields(out, &values[16])?;
                                  let a ← Array.index_usize values 16#usize
                                  let s ← lift (Array.to_slice a)
                                  tryUnit (fields out s) fun out => do
                                    -- frozen line 2047: fields(out, &values[17])?;
                                    let a ← Array.index_usize values 17#usize
                                    let s ← lift (Array.to_slice a)
                                    tryUnit (fields out s) fun out => do
                                      -- frozen line 2048: fields(out, &values[18])?;
                                      let a ← Array.index_usize values 18#usize
                                      let s ← lift (Array.to_slice a)
                                      tryUnit (fields out s) fun out => do
                                        -- frozen line 2049: fields(out, &values[19])?;
                                        let a ← Array.index_usize values 19#usize
                                        let s ← lift (Array.to_slice a)
                                        tryUnit (fields out s) fun out => do
                                          -- frozen line 2050: Ok(())
                                          ok (core.result.Result.Ok (), out)

/-- frozen 2017-2077 `pub fn public_bytes(self) -> Result<Vec<u8>, Error>`. -/
def public_bytes
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)
  := do
  let p ← semantic self                                                  -- 2052 let p = self.semantic();
  let out ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8)                -- 2053 let mut out = Vec::new();
    (match p.variant with                                                -- 2054 out.push(match p.variant {
     | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer => 0#u8  -- 2055
     | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal => 1#u8)      -- 2056-2057
  let s ← lift (Array.to_slice p.anchor)                                 -- 2058 fields(&mut out, &p.anchor)?;
  tryTop (fields out s) fun out => do
    let s ← lift (Array.to_slice p.nullifier)                            -- 2059 fields(&mut out, &p.nullifier)?;
    tryTop (fields out s) fun out => do
      let s ← lift (Array.to_slice (Array.make 1#usize [ p.asset_id ]))  -- 2060 fields(&mut out, &[p.asset_id])?;
      tryTop (fields out s) fun out => do
        let b := core.option.Option.is_some p.recipient                  -- 2061 out.push(u8::from(p.recipient.is_some()));
        let i ← lift (core.convert.num.FromU8Bool.from b)
        let out ← alloc.vec.Vec.push out i
        ifSomeFields p.recipient out (fun value => Array.to_slice value) fun out => do  -- 2062-2064
          let s ← lift (Array.to_slice p.change)                         -- 2065 fields(&mut out, &p.change)?;
          tryTop (fields out s) fun out => do
            let b1 := core.option.Option.is_some p.withdrawal_amount     -- 2066 out.push(u8::from(p.withdrawal_amount.is_some()));
            let i1 ← lift (core.convert.num.FromU8Bool.from b1)
            let out ← alloc.vec.Vec.push out i1
            ifSomeFields p.withdrawal_amount out                         -- 2067-2069 fields(&mut out, &[M31(value)])?;
              (fun value => Array.to_slice (Array.make 1#usize [ value ])) fun out => do
              let source := p.transition.live_snapshot                   -- 2070
              let after := p.transition.candidate_afterstate             -- 2071
              let a ← lift (core.num.U64.to_le_bytes source.next_pair_index)  -- 2072 out.extend_from_slice(&source.next_pair_index.to_le_bytes());
              let s ← lift (Array.to_slice a)
              let out ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
              tryTop (frontier out source.frontier) fun out => do        -- 2073 frontier(&mut out, &source.frontier)?;
                let s ← lift (Array.to_slice after.next_root)            -- 2074 fields(&mut out, &after.next_root)?;
                tryTop (fields out s) fun out => do
                  tryTop (frontier out after.next_frontier) fun out =>   -- 2075 frontier(&mut out, &after.next_frontier)?;
                    ok (core.result.Result.Ok out)                       -- 2076 Ok(out)

end NPL_PublicBytesRef
