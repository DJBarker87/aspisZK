# NPL_ public_bytes: gate definition = hand transcription of the frozen accessor

Stream A job NPL_, 2026-11-10. Target not yet established. Class of the result: **ReviewedTranscription** (AGENTS.md section 3). The Lean file `NPL_PublicBytesRef.lean` is a hand transcription, not an Aeneas emission; what is machine-checked is that the gate constant equals that transcription and that it is total with a fixed output length. Whether the transcription preserves the frozen Rust behaviour is a reviewed claim, recorded below as a proposed trust-inventory line.

## 1. Frozen Rust (revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387)

File `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`, file sha256 `4e209947ac75532af1c7d79f339050aab6b57379fc3962e1df9ff5602087787e`.

`r0::Public::public_bytes`, lines 2017-2077 (sha256 of exactly these lines, newline-terminated: `46feab6146ac57be857df3082aaa7258cb870dcf5c2ba90883b453574138a312`):

```rust
        pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
            fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error> {
                for value in values {
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
                }
                Ok(())
            }
            // The fixed width is checked at both call sites. Explicit calls
            // avoid nested frontier loops during source extraction.
            fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error> {
                fields(out, &values[0])?;
                fields(out, &values[1])?;
                fields(out, &values[2])?;
                fields(out, &values[3])?;
                fields(out, &values[4])?;
                fields(out, &values[5])?;
                fields(out, &values[6])?;
                fields(out, &values[7])?;
                fields(out, &values[8])?;
                fields(out, &values[9])?;
                fields(out, &values[10])?;
                fields(out, &values[11])?;
                fields(out, &values[12])?;
                fields(out, &values[13])?;
                fields(out, &values[14])?;
                fields(out, &values[15])?;
                fields(out, &values[16])?;
                fields(out, &values[17])?;
                fields(out, &values[18])?;
                fields(out, &values[19])?;
                Ok(())
            }
            let p = self.semantic();
            let mut out = Vec::new();
            out.push(match p.variant {
                CompiledVariant::PrivateTransfer => 0,
                CompiledVariant::Withdrawal => 1,
            });
            fields(&mut out, &p.anchor)?;
            fields(&mut out, &p.nullifier)?;
            fields(&mut out, &[p.asset_id])?;
            out.push(u8::from(p.recipient.is_some()));
            if let Some(value) = p.recipient {
                fields(&mut out, &value)?;
            }
            fields(&mut out, &p.change)?;
            out.push(u8::from(p.withdrawal_amount.is_some()));
            if let Some(value) = p.withdrawal_amount {
                fields(&mut out, &[M31(value)])?;
            }
            let source = p.transition.live_snapshot;
            let after = p.transition.candidate_afterstate;
            out.extend_from_slice(&source.next_pair_index.to_le_bytes());
            frontier(&mut out, &source.frontier)?;
            fields(&mut out, &after.next_root)?;
            frontier(&mut out, &after.next_frontier)?;
            Ok(out)
        }
```

Callee `r0::Public::semantic`, lines 2005-2010 (sha256 `7752d85a8842d6fb7e9dc04c55de924be7063e8c742c8d07b811186b11c47383`):

```rust
        fn semantic(self) -> SemanticPublic<'a> {
            match self {
                Self::Transfer(public, transition) => private_public(public, transition),
                Self::Withdrawal(public, transition) => withdrawal_public(public, transition),
            }
        }
```

Callees `private_public` and `withdrawal_public`, lines 1327-1361 (sha256 `7465061c60e2ced927a64349f0d154248c4ea63a954c4a96cd4723ec462e032a`):

```rust
fn private_public<'a>(
    public: &PoolV1PrivateTransferPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::PrivateTransfer,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: Some(public.recipient_commitment),
        change: public.change_commitment,
        withdrawal_amount: None,
        transition,
    }
}

fn withdrawal_public<'a>(
    public: &PoolV1WithdrawalPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::Withdrawal,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: None,
        change: public.change_commitment,
        withdrawal_amount: Some(public.amount),
        transition,
    }
}
```

Constants and carriers used (same revision): `crates/aspis-core/src/field.rs:19` `pub const P: u32 = 0x7fff_ffff;` and `:23` `pub struct M31(pub u32);` (file sha256 `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`); `crates/aspis-statement/src/poseidon2.rs:58,60` `DIGEST_ELEMS = 8`, `type Digest = [M31; DIGEST_ELEMS]` (sha256 `4563a719...a1740`); `pool_v1/pair_tree_profile.rs:404-419` (`PoolV1PairLiveSnapshotV1`, `PoolV1PairLatePublicStatementV1`; sha256 `660f00d9...e7af`); `pool_v1/payment_relation.rs:46-68` (`PoolV1PrivateTransferPublicV1`, `PoolV1WithdrawalPublicV1`; sha256 `5651470e...b49d`); `pool_v1/pair_terminal.rs:116-120` (`PoolV1PairVerifiedAfterstateV1`; sha256 `03fc1412...bbea`); `POOL_V1_PAIR_TREE_DEPTH = POOL_V1_TREE_DEPTH = 20` (`pair_tree_profile.rs:33`, `format.rs:28`). The fields read by `public_bytes` have the same names, order and types in the gate's `AspisR1PublicPreparation.Types` carriers.

## 2. Gate definition (AspisR1PublicPreparation/Funs.lean)

Committed copy `docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean`, sha256 `544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d` (equal to every compiled gate constant, PCVJ_L003). Compiled object used here: `/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104/AspisR1PublicPreparation/Funs.olean` sha256 `933f376d3f58f29770fa585d0df01f1ef4f1b377a205e8a9219b72f8a4b3f07f` (the same object pinned by PCVJ_L003 and PCVL_L007).

The full verbatim text of the eight gate definitions in the `public_bytes` closure (Funs.lean lines 885-1877: `private_public`, `withdrawal_public`, `r0.Public.semantic`, `public_bytes.fields_loop.body`, `public_bytes.fields_loop`, `public_bytes.fields`, `public_bytes.frontier`, `public_bytes`) is in `NPL_GATE_VERBATIM.lean.txt` (sha256 `2f8b11c99fa54f900e6c8cad3336fa253e8e884ce08e6131a15c32b290959d9f`). The gate was emitted by Aeneas from a mirror crate (`aspis_r1_public_preparation`, `lib.rs` lines 281:8-341:9 for `public_bytes`), not from the frozen file above; that is why the comparison has to go through a transcription of the frozen text. Opening of the gate `public_bytes` and its loop body:

```lean
/-- [aspis_r1_public_preparation::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_public_preparation::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes]:
    Source: 'lib.rs', lines 281:8-341:9
    Visibility: public -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)
  := do
  let p ← pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self
  match p.variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let out ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8) 0#u8
    let s ← lift (Array.to_slice p.anchor)
    let (r, out1) ←
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← lift (Array.to_slice p.nullifier)
      let (r1, out2) ←
        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
          out1 s1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← lift (Array.to_slice (Array.make 1#usize [ p.asset_id ]))
        let (r2, out3) ←
          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
            out2 s2
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let b := core.option.Option.is_some p.recipient
...
```

```lean
    Source: 'lib.rs', lines 283:16-290:13 -/
@[rust_loop_body]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.M31) ×
    (alloc.vec.Vec Std.U8)) ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok (), out))
  | some value =>
    if value >= aspis_core.field.P
    then
      ok (done (core.result.Result.Err
        aspis_core.state_only_prefix.r0.Error.Public, out))
    else
      let a ← lift (core.num.U32.to_le_bytes value)
      let s ← lift (Array.to_slice a)
      let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
      ok (cont (iter1, out1))

/-- [aspis_r1_public_preparation::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_public_preparation::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes::fields]: loop 0:
```

Exact gate names: `AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes : pool_v1.pair_forest_semantic_terminal.r0.Public → Result (core.result.Result (alloc.vec.Vec Std.U8) aspis_core.state_only_prefix.r0.Error)`; this is the constant that `r1_semantic.public_transcript` calls in `evidence/prov-p3l-20261110/PRVEq_PP_l4.lean` (line 143).

## 3. Hand transcription (NPL_PublicBytesRef.lean)

`NPL_PublicBytesRef.lean` (sha256 `05572e6a5b4d2cb4caa6a819e385e081196a719048f00cd8eee3921e90ddcd46`) imports `Aeneas` and `AspisR1PublicPreparation.Types` only: it uses the gate's carrier types but no gate function or constant (it defines its own `P`). Every line carries the frozen line number it transcribes. Carrier conventions (each part of the reviewed claim): `M31(pub u32)` is the gate's `aspis_core.field.M31 := Std.U32`, so `value.0` and `M31(value)` are `value`; `Digest` is `Array M31 8#usize`; `&mut out` is threaded and returned on both paths; Rust `?` is the Aeneas `Try::branch`/`FromResidual::from_residual` pair (helpers `tryUnit`, `tryTop`); `for value in values` is `into_iter` then `loop` over `Iterator::next`; Aeneas `fail` models a Rust panic (here only Vec capacity overflow). Structurally the transcription follows the Rust: one `push` of a `match`-computed tag, sequential `?` calls through continuation helpers, and an `ifSomeFields` helper for each `if let Some`, where the gate duplicates the continuation into every branch.

```lean
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
```

The other definitions (`P`, `private_public`, `withdrawal_public`, `semantic`, `fields_loop`, `fields`, `tryUnit`, `tryTop`, `ifSomeFields`, and `frontier` with its twenty explicit calls at lines 2030-2049) are in the file with the same per-line comments. `NPL_gen.py` writes both Lean files; the only generated text is the twenty repeated `frontier` calls and the twenty matching proof steps.

## 4. Theorems (NPL_PublicBytes.lean, sha256 `162eae0d961576e7da7a930aaab39e0a5ff296b80be486904bbc3e803d36057e`)

- `NPL_PublicBytes.gate_eq : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes = NPL_PublicBytesRef.public_bytes` (equality of functions, so on all arguments). It is built from `P_eq` (gate `aspis_core.field.P` = `2147483647#u32`), `private_public_eq`, `withdrawal_public_eq`, `semantic_eq`, `fields_loop_body_eq`, `fields_loop_eq`, `fields_eq` and `frontier_eq`, each an equality between the gate constant and the transcription constant. The proofs are definitional unfolding plus case analysis on the `Public` constructor (no evaluation of large terms).
- `NPL_PublicBytes.gate_total_length (self) : ∃ r, gate.public_bytes self = ok r ∧ ∀ v, r = core.result.Result.Ok v → v.val.length = expected_len self`, with `expected_len (Transfer _ _) = 1455` (1+32+32+4+1+32+32+1+8+640+32+640) and `expected_len (Withdrawal _ _) = 1427` (1+32+32+4+1+32+1+4+8+640+32+640). On every input the gate returns `ok` (never `fail` or `div`, i.e. the modelled body never panics or diverges), and an `Ok` output has the fixed length. The proof shows `fields` adds exactly `4 * len` bytes when it returns `Ok` (induction over the `loop` unfolding), and that every `Vec.push` / `Vec.extend_from_slice` / `Array.index_usize` call is in bounds (`4294967295 ≤ Usize.max`). The `Err(Error::Public)` path (some field value `≥ P`) is covered by totality; its exact error value is not stated.

No `sorry`, `axiom`, `native_decide` or raised heartbeat/recursion limit appears in either file.

## 5. Receipt

| item | value |
|---|---|
| target | one scope: `lake env lean -j1 -M7000 -DElab.async=false -R NPL_sources -o NPL_exports/NPL_PublicBytesRef.olean NPL_sources/NPL_PublicBytesRef.lean && (same) NPL_PublicBytes.lean` (attempt NPL_L002) |
| exit | 0 |
| wall | 4.03 s (whole command, both files) |
| peak RSS | 2698936 KiB; cgroup memory.peak 364740608 bytes |
| swap | swaps 0; scope MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64, timeout 180 s |
| host | `/home/dombarker/project-offloads/codex-cx-pb-20261110` (own workspace); toolchain leanprover--lean4---v4.32.0 |
| LEAN_PATH | `NPL_exports` : `codex-cx-replay-l187-20261109/base_ref` (Aeneas/Mathlib closure of the L187 replay; `Aeneas.olean` resolves to NNG119_seed, sha256 d3bfce81...) : `codex-cx-pool-retarget-cache-20261104` (gate module only). All 241 selected objects are hash-pinned in `NPL_L002/receipt.json` |
| source revision | branch codex/cx-pb-20261110 at 44c36fb524e plus these uncommitted files (`source_tree_dirty: true`); the compiled sources' sha256 in the receipt equal the committed files above |
| objects | NPL_PublicBytesRef.olean sha256 bbc92973...3342; NPL_PublicBytes.olean sha256 48867e60...03ac (`NPL_L002-object.json`) |

`#print axioms` (NPL_L002):

```
'NPL_PublicBytes.P_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.private_public_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.withdrawal_public_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.semantic_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.fields_loop_body_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.fields_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.fields_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.frontier_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.gate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPL_PublicBytes.gate_total_length' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Failed attempt kept: NPL_L001 (exit 1, 4.12 s, peak RSS 2671700 KiB, swaps 0). The transcription and every equality theorem, `gate_eq` included, were already green in L001 with the same axioms. The failures were in the section-4 length lemmas only: `spec_imp_exists` is `Aeneas.Std.WP.spec_imp_exists` (wrong namespace); in `body_done`/`body_step`, `simp only` did not reduce the do-notation pair match after `bind`, so `split` found nothing to split. Replacement in L002: `WP.spec_imp_exists`, `rfl` after the rewrite, and an explicit `rfl`-proved unfolding (`h1`) followed by `if_pos`/`if_neg`. Lean scopes used: 2 of 6.

## 6. What changed in the obligation

Before: `PRVEq_PP_l4.lean` (PCVL_L007) proves the fresh PublicPreparation emission equal to the gate, CONDITIONAL_ON_BINDING on `pool_v1 Public.public_bytes`. The fresh emission's `public_transcript` calls the gate constant by name, and that constant was related to nothing frozen (Aeneas failed twice on the frozen accessor; the shape is retired).
After: the gate constant is proved equal (`gate_eq`) to a hand transcription of the frozen accessor at the lines and hashes above, and is total with fixed output length (`gate_total_length`). The binding for `public_bytes` is therefore narrowed from "unrelated gate constant" to one ReviewedTranscription item. It is not discharged to a machine-checked source refinement. `core.result.Result.map_err` (HM-C) is untouched and still binds PRVEq_PP_l4.

Not claimed: that the gate's carrier types are the frozen Rust types (field correspondence was checked by reading, not by proof); anything about the bytes' contents beyond the transcription; Rust allocation failure (OOM abort lies outside the Aeneas model); `transition`, `terminal`, `terminal_qm31`, or any other `Public` method.

## 7. Proposed trust-inventory line (not added; for the owner/lead)

ReviewedTranscription-PublicPreparation.public_bytes (ADDED-LEAD-20261110): the Lean transcription NPL_PublicBytesRef.public_bytes of the frozen accessor at crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017-2077 (with callees semantic 2005-2010, private_public/withdrawal_public 1327-1361; file sha256 4e209947ac75532af1c7d79f339050aab6b57379fc3962e1df9ff5602087787e, lines sha256 46feab6146ac57be857df3082aaa7258cb870dcf5c2ba90883b453574138a312, revision 4bb3b3f) preserves its behaviour; the gate definition is proved equal to it (NPL_PublicBytes.gate_eq; total with fixed length, NPL_PublicBytes.gate_total_length); removal condition: an Aeneas emission of public_bytes proved equal.

Target not yet established.
