#!/usr/bin/env python3
"""NPL_ generator: writes NPL_PublicBytesRef.lean (hand transcription) and NPL_PublicBytes.lean (proofs).
The only generated parts are the twenty repeated `fields(out, &values[j])?;` calls of `frontier` and the
matching twenty proof steps; everything else is literal text below."""
from pathlib import Path
E = Path(__file__).resolve().parent

ERR = "aspis_core.state_only_prefix.r0.Error"
UNITR = f"((core.result.Result Unit {ERR}) × (alloc.vec.Vec Std.U8))"
TOPR = f"(core.result.Result (alloc.vec.Vec Std.U8) {ERR})"

def frontier_body():
    lines = []
    ind = "  "
    for j in range(20):
        lines.append(f"{ind}-- frozen line {2030 + j}: fields(out, &values[{j}])?;")
        lines.append(f"{ind}let a ← Array.index_usize values {j}#usize")
        lines.append(f"{ind}let s ← lift (Array.to_slice a)")
        lines.append(f"{ind}tryUnit (fields out s) fun out => do")
        ind += "  "
    lines.append(f"{ind}-- frozen line 2050: Ok(())")
    lines.append(f"{ind}ok (core.result.Result.Ok (), out)")
    return "\n".join(lines)

REF = f'''-- NPL_PublicBytesRef.lean (Stream A job NPL_, 2026-11-10)
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
--   * Rust `Result<T, Error>` is `core.result.Result T {ERR}` inside the Aeneas `Result` monad;
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
    {{
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
    }}

/-- frozen 1345-1361 `fn withdrawal_public(public, transition) -> SemanticPublic`. -/
def withdrawal_public
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {{
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
    }}

/-- frozen 2005-2010 `fn semantic(self) -> SemanticPublic {{ match self {{ .. }} }}`. -/
def semantic
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer public1 transition =>     -- 2007
    private_public public1 transition
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal public1 transition =>   -- 2008
    withdrawal_public public1 transition

/-- frozen 2019-2024, one iteration of `for value in values {{ .. }}` inside `fn fields`. -/
def fields_loop.body
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.M31) ×
    (alloc.vec.Vec Std.U8)) {UNITR})
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter        -- 2019 for value in values
  match o with
  | none => ok (done (core.result.Result.Ok (), out))                  -- 2024 loop ends; 2025 Ok(())
  | some value =>
    if value >= P                                                      -- 2020 if value.0 >= P
    then
      ok (done (core.result.Result.Err {ERR}.Public, out))             -- 2021 return Err(Error::Public)
    else
      let a ← lift (core.num.U32.to_le_bytes value)                    -- 2023 value.0.to_le_bytes()
      let s ← lift (Array.to_slice a)                                  -- 2023 &[u8; 4] as &[u8]
      let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s  -- 2023 out.extend_from_slice
      ok (cont (iter1, out1))

/-- frozen 2019-2024 the loop itself. -/
def fields_loop
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result {UNITR}
  := do
  loop (fun (iter1, out1) => NPL_PublicBytesRef.fields_loop.body iter1 out1) (iter, out)

/-- frozen 2018-2026 `fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error>`. -/
def fields
  (out : alloc.vec.Vec Std.U8) (values : Slice aspis_core.field.M31) :
  Result {UNITR}
  := do
  let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values  -- 2019
  fields_loop iter out

/-- Rust `e?;` inside a helper returning `Result<(), Error>` that holds `out: &mut Vec<u8>`:
    on `Ok` continue with `k`; on `Err` return the converted residual and the current `out`. -/
def tryUnit
  (x : Result {UNITR})
  (k : alloc.vec.Vec Std.U8 → Result {UNITR}) :
  Result {UNITR}
  := do
  let (r, out1) ← x
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => k out1
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame {ERR}) residual
    ok (r1, out1)

/-- Rust `e?;` inside `public_bytes` (returns `Result<Vec<u8>, Error>`; the local `out` is dropped
    on the error path). -/
def tryTop
  (x : Result {UNITR})
  (k : alloc.vec.Vec Std.U8 → Result {TOPR}) :
  Result {TOPR}
  := do
  let (r, out1) ← x
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => k out1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame {ERR}) residual

/-- Rust `if let Some(value) = o {{ fields(&mut out, <slice of value>)?; }}` followed by the rest `k`. -/
def ifSomeFields {{α : Type}}
  (o : Option α) (out : alloc.vec.Vec Std.U8) (slice : α → Slice aspis_core.field.M31)
  (k : alloc.vec.Vec Std.U8 → Result {TOPR}) :
  Result {TOPR}
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
  Result {UNITR}
  := do
{frontier_body()}

/-- frozen 2017-2077 `pub fn public_bytes(self) -> Result<Vec<u8>, Error>`. -/
def public_bytes
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result {TOPR}
  := do
  let p ← semantic self                                                  -- 2052 let p = self.semantic();
  let out ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8)                -- 2053 let mut out = Vec::new();
    (match p.variant with                                                -- 2054 out.push(match p.variant {{
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
'''

# ---------------------------------------------------------------- proofs
G = "AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public"
R = "NPL_PublicBytesRef"

def frontier_steps():
    out = []
    prev = "out"
    for j in range(20):
        o = f"o{j+1}"
        out.append(f"  refine idx_step values _ (by npl_idx) {prev} _ (by omega) (fun {o} h{j+1} => ?_)")
        prev = o
    out.append("  exact ⟨_, o20, rfl, fun _ => by omega⟩")
    return "\n".join(out)

PROOF = f'''-- NPL_PublicBytes.lean (Stream A job NPL_, 2026-11-10)
-- The gate definition of `public_bytes` (and its callees) is proved equal to the hand transcription
-- NPL_PublicBytesRef of the frozen Rust accessor; plus totality and output length.
import Aeneas
import AspisR1PublicPreparation.Funs
import NPL_PublicBytesRef
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NPL_PublicBytes
open AspisR1PublicPreparation

/-! ## 1. Gate = transcription -/

theorem P_eq : aspis_core.field.P = {R}.P := by
  first
  | (unfold aspis_core.field.P {R}.P; rfl)
  | (with_unfolding_all rfl)
  | (simp [aspis_core.field.P, {R}.P])

theorem private_public_eq :
    pool_v1.pair_forest_semantic_terminal.private_public = {R}.private_public := by
  funext a b; rfl

theorem withdrawal_public_eq :
    pool_v1.pair_forest_semantic_terminal.withdrawal_public = {R}.withdrawal_public := by
  funext a b; rfl

theorem semantic_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.semantic = {R}.semantic := by
  funext self; cases self <;> rfl

theorem fields_loop_body_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body =
      {R}.fields_loop.body := by
  funext iter out
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
    {R}.fields_loop.body
  first
  | rw [P_eq]
  | simp only [P_eq]
  all_goals rfl

theorem fields_loop_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop =
      {R}.fields_loop := by
  funext iter out
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop
    {R}.fields_loop
  first
  | rw [fields_loop_body_eq]
  | simp only [fields_loop_body_eq]
  all_goals rfl

theorem fields_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields = {R}.fields := by
  funext out values
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields {R}.fields
  first
  | rw [fields_loop_eq]
  | simp only [fields_loop_eq]
  all_goals rfl

theorem frontier_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier = {R}.frontier := by
  funext out values
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier {R}.frontier
  first
  | rw [fields_eq]
  | simp only [fields_eq]
  all_goals first
  | rfl
  | (simp only [{R}.tryUnit]; rfl)

/-- Main equality: the gate constant equals the hand transcription of the frozen accessor. -/
theorem gate_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes = {R}.public_bytes := by
  funext self
  cases self <;>
    (unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes {R}.public_bytes
     first
     | rw [fields_eq, frontier_eq, semantic_eq]
     | simp only [fields_eq, frontier_eq, semantic_eq]
     all_goals first
     | rfl
     | (simp only [{R}.semantic, {R}.private_public, {R}.withdrawal_public, bind_tc_ok,
         {R}.tryTop, {R}.ifSomeFields]; rfl))

/-! ## 2. Totality and output length -/

abbrev Good (n : Nat) (res : Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) ×
    (alloc.vec.Vec Std.U8))) : Prop :=
  ∃ r out', res = ok (r, out') ∧ (r = core.result.Result.Ok () → out'.val.length = n)

abbrev TGood (n : Nat) (res : Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)) : Prop :=
  ∃ r, res = ok r ∧ ∀ v, r = core.result.Result.Ok v → v.val.length = n

theorem usize_ge : 4294967295 ≤ Usize.max := by
  first
  | scalar_tac
  | (rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits])
  | (rcases Usize.bounds_eq with h | h <;> rw [h] <;> decide)

macro "npl_idx" : tactic => `(tactic| first | scalar_tac | (simp; scalar_tac) | decide | simp)

theorem len_slice {{α : Type}} {{n : Usize}} (a : Array α n) :
    (Array.to_slice a).val.length = n.val := a.property

theorem len_lit8 {{α : Type}} (a : Array α 8#usize) : (Array.to_slice a).val.length = 8 := by
  rw [len_slice]; first | rfl | simp | scalar_tac

theorem len_lit4 {{α : Type}} (a : Array α 4#usize) : (Array.to_slice a).val.length = 4 := by
  rw [len_slice]; first | rfl | simp | scalar_tac

theorem len_one {{α : Type}} (x : α) :
    (Array.to_slice (Array.make 1#usize [ x ])).val.length = 1 := by
  first | rfl | simp [Array.to_slice, Array.make] | scalar_tac

theorem extend_good (v : alloc.vec.Vec Std.U8) (s : Slice Std.U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    ∃ v' : alloc.vec.Vec Std.U8, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok v' ∧
      v'.val.length = v.val.length + s.val.length := by
  obtain ⟨s', hc, hss⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s) (fun x _ => rfl))
  unfold alloc.vec.Vec.extend_from_slice
  split
  · split
    · rename_i s'' heq
      refine ⟨_, rfl, ?_⟩
      have hl := Slice.clone_length heq
      simp only [Slice.length] at hl
      simp only [List.length_append, hl]
    · rename_i e heq; rw [hc] at heq; cases heq
    · rename_i heq; rw [hc] at heq; cases heq
  · rename_i hh; exact absurd h hh

theorem push_good (v : alloc.vec.Vec Std.U8) (x : Std.U8) (h : v.val.length + 1 ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val.length = v.val.length + 1 := by
  obtain ⟨v', hv, hl⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec v x (by omega))
  exact ⟨v', hv, by rw [hl, List.length_append]; rfl⟩

theorem next_some {{α : Type}} (s : Slice α) (i : Nat) (hi : i < s.val.length) :
    ∃ x, core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter α) =
      ok (some x, ⟨s, i + 1⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · exact ⟨_, rfl⟩
  · rename_i hc; exfalso; apply hc; simpa [Slice.len_val] using hi

theorem next_none {{α : Type}} (s : Slice α) (i : Nat) (hi : ¬ i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter α) = ok (none, ⟨s, i⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i hc; exfalso; apply hi; simpa [Slice.len_val] using hc
  · rfl

theorem body_done (s : Slice aspis_core.field.M31) (i : Nat) (out : alloc.vec.Vec Std.U8)
    (hi : ¬ i < s.val.length) :
    {R}.fields_loop.body ⟨s, i⟩ out = ok (done (core.result.Result.Ok (), out)) := by
  unfold {R}.fields_loop.body
  rw [next_none s i hi]
  all_goals first | rfl | simp

theorem body_step (s : Slice aspis_core.field.M31) (i : Nat) (out : alloc.vec.Vec Std.U8)
    (hi : i < s.val.length) (hb : out.val.length + 4 ≤ Usize.max) :
    (∃ e, {R}.fields_loop.body ⟨s, i⟩ out = ok (done (core.result.Result.Err e, out))) ∨
    (∃ out', {R}.fields_loop.body ⟨s, i⟩ out = ok (cont (⟨s, i + 1⟩, out')) ∧
      out'.val.length = out.val.length + 4) := by
  obtain ⟨x, hx⟩ := next_some s i hi
  have h1 : {R}.fields_loop.body ⟨s, i⟩ out =
      (if x >= {R}.P then
        ok (done (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public, out))
      else do
        let a ← lift (core.num.U32.to_le_bytes x)
        let s' ← lift (Array.to_slice a)
        let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s'
        ok (cont ((⟨s, i + 1⟩ : core.slice.iter.Iter aspis_core.field.M31), out1))) := by
    unfold {R}.fields_loop.body
    rw [hx]
    all_goals rfl
  rw [h1]
  by_cases hp : x >= {R}.P
  · left
    exact ⟨aspis_core.state_only_prefix.r0.Error.Public, by rw [if_pos hp]⟩
  · right
    obtain ⟨v', hv, hl⟩ := extend_good out (Array.to_slice (core.num.U32.to_le_bytes x))
      (by rw [len_lit4]; exact hb)
    refine ⟨v', ?_, by rw [hl, len_lit4]⟩
    rw [if_neg hp]
    simp only [lift, bind_tc_ok, hv]

theorem fields_loop_good (s : Slice aspis_core.field.M31) :
    ∀ (k i : Nat) (out : alloc.vec.Vec Std.U8), s.val.length = i + k →
      out.val.length + 4 * k ≤ Usize.max →
      Good (out.val.length + 4 * k) ({R}.fields_loop ⟨s, i⟩ out) := by
  intro k
  induction k with
  | zero =>
    intro i out hs hb
    have hd := body_done s i out (by omega)
    unfold {R}.fields_loop
    first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
    simp only [hd]
    exact ⟨_, out, rfl, fun _ => by omega⟩
  | succ k ih =>
    intro i out hs hb
    rcases body_step s i out (by omega) (by omega) with ⟨e, he⟩ | ⟨out', he, hl⟩
    · unfold {R}.fields_loop
      first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
      simp only [he]
      exact ⟨_, out, rfl, fun h => by cases h⟩
    · have ih' := ih (i + 1) out' (by omega) (by omega)
      have e : out'.val.length + 4 * k = out.val.length + 4 * (k + 1) := by omega
      rw [e] at ih'
      unfold {R}.fields_loop at ih' ⊢
      first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
      simp only [he]
      exact ih'

theorem fields_good (out : alloc.vec.Vec Std.U8) (s : Slice aspis_core.field.M31) (n c : Nat)
    (hn : out.val.length = n) (hc : s.val.length = c) (hb : n + 4 * c ≤ Usize.max) :
    Good (n + 4 * c) ({R}.fields out s) := by
  have := fields_loop_good s c 0 out (by omega) (by omega)
  rw [hn] at this
  unfold {R}.fields
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok,
    bind_ok]
  exact this

theorem tryUnit_good {{m n : Nat}} {{x : Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}}
    {{k : alloc.vec.Vec Std.U8 → Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}}
    (hx : Good n x) (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n → Good m (k o)) :
    Good m ({R}.tryUnit x k) := by
  obtain ⟨r, o, hx, hr⟩ := hx
  cases r with
  | Ok u =>
    cases u
    have := hk o (hr rfl)
    simpa [{R}.tryUnit, hx, core.result.Result.Insts.CoreOpsTry.branch] using this
  | Err e =>
    refine ⟨core.result.Result.Err e, o, ?_, fun h => by cases h⟩
    simp [{R}.tryUnit, hx, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

theorem tryTop_good {{m n : Nat}} {{x : Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}}
    {{k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)}}
    (hx : Good n x) (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n → TGood m (k o)) :
    TGood m ({R}.tryTop x k) := by
  obtain ⟨r, o, hx, hr⟩ := hx
  cases r with
  | Ok u =>
    cases u
    have := hk o (hr rfl)
    simpa [{R}.tryTop, hx, core.result.Result.Insts.CoreOpsTry.branch] using this
  | Err e =>
    refine ⟨core.result.Result.Err e, ?_, fun v h => by cases h⟩
    simp [{R}.tryTop, hx, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

theorem idx_step {{m : Nat}} (values : Array (Array aspis_core.field.M31 8#usize) 20#usize)
    (j : Usize) (hj : j.val < values.val.length) (out : alloc.vec.Vec Std.U8)
    (k : alloc.vec.Vec Std.U8 → Result ((core.result.Result Unit
      aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
    (hb : out.val.length + 32 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = out.val.length + 32 → Good m (k o)) :
    Good m (do
      let a ← Array.index_usize values j
      let s ← lift (Array.to_slice a)
      {R}.tryUnit ({R}.fields out s) k) := by
  obtain ⟨a, ha, -⟩ := WP.spec_imp_exists (Array.index_usize_spec values j hj)
  rw [ha]
  simp only [bind_tc_ok, bind_ok, lift]
  exact tryUnit_good (fields_good out (Array.to_slice a) _ 8 rfl (len_lit8 a) (by omega)) hk

theorem frontier_good (out : alloc.vec.Vec Std.U8)
    (values : Array (Array aspis_core.field.M31 8#usize) 20#usize)
    (hb : out.val.length + 640 ≤ Usize.max) :
    Good (out.val.length + 640) ({R}.frontier out values) := by
  unfold {R}.frontier
{frontier_steps()}

theorem top_push {{m n : Nat}} {{v : alloc.vec.Vec Std.U8}} {{x : Std.U8}}
    {{k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}}
    (hn : v.val.length = n) (hb : n + 1 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 1 → TGood m (k o)) :
    TGood m (alloc.vec.Vec.push v x >>= k) := by
  obtain ⟨v', hv, hl⟩ := push_good v x (by omega)
  rw [hv]; simp only [bind_tc_ok, bind_ok]; exact hk v' (by omega)

theorem top_extend {{m n c : Nat}} {{v : alloc.vec.Vec Std.U8}} {{s : Slice Std.U8}}
    {{k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}}
    (hn : v.val.length = n) (hc : s.val.length = c) (hb : n + c ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + c → TGood m (k o)) :
    TGood m (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s >>= k) := by
  obtain ⟨v', hv, hl⟩ := extend_good v s (by omega)
  rw [hv]; simp only [bind_tc_ok, bind_ok]; exact hk v' (by omega)

theorem top_fields {{m n c : Nat}} {{out : alloc.vec.Vec Std.U8}} {{s : Slice aspis_core.field.M31}}
    {{k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}}
    (hn : out.val.length = n) (hc : s.val.length = c) (hb : n + 4 * c ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 4 * c → TGood m (k o)) :
    TGood m ({R}.tryTop ({R}.fields out s) k) :=
  tryTop_good (fields_good out s n c hn hc hb) hk

theorem top_frontier {{m n : Nat}} {{out : alloc.vec.Vec Std.U8}}
    {{values : Array (Array aspis_core.field.M31 8#usize) 20#usize}}
    {{k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}}
    (hn : out.val.length = n) (hb : n + 640 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 640 → TGood m (k o)) :
    TGood m ({R}.tryTop ({R}.frontier out values) k) := by
  have := frontier_good out values (by omega)
  rw [hn] at this
  exact tryTop_good this hk

/-- Expected output length: Transfer 1+32+32+4+1+32+32+1+8+640+32+640 = 1455;
    Withdrawal 1+32+32+4+1+32+1+4+8+640+32+640 = 1427. -/
def expected_len : pool_v1.pair_forest_semantic_terminal.r0.Public → Nat
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer _ _ => 1455
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal _ _ => 1427

theorem ref_public_bytes_good (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    TGood (expected_len self) ({R}.public_bytes self) := by
  have U := usize_ge
  cases self with
  | Transfer pub1 tr =>
    simp only [{R}.public_bytes, {R}.semantic, {R}.private_public, {R}.ifSomeFields, lift,
      bind_tc_ok, bind_ok, expected_len]
    refine top_push (n := 0) rfl (by omega) (fun o1 h1 => ?_)
    refine top_fields h1 (len_lit8 _) (by omega) (fun o2 h2 => ?_)
    refine top_fields h2 (len_lit8 _) (by omega) (fun o3 h3 => ?_)
    refine top_fields h3 (len_one _) (by omega) (fun o4 h4 => ?_)
    refine top_push h4 (by omega) (fun o5 h5 => ?_)
    refine top_fields h5 (len_lit8 _) (by omega) (fun o6 h6 => ?_)
    refine top_fields h6 (len_lit8 _) (by omega) (fun o7 h7 => ?_)
    refine top_push h7 (by omega) (fun o8 h8 => ?_)
    refine top_extend h8 (len_lit8 _) (by omega) (fun o9 h9 => ?_)
    refine top_frontier h9 (by omega) (fun o10 h10 => ?_)
    refine top_fields h10 (len_lit8 _) (by omega) (fun o11 h11 => ?_)
    refine top_frontier h11 (by omega) (fun o12 h12 => ?_)
    exact ⟨_, rfl, fun v hv => by cases hv; omega⟩
  | Withdrawal pub1 tr =>
    simp only [{R}.public_bytes, {R}.semantic, {R}.withdrawal_public, {R}.ifSomeFields, lift,
      bind_tc_ok, bind_ok, expected_len]
    refine top_push (n := 0) rfl (by omega) (fun o1 h1 => ?_)
    refine top_fields h1 (len_lit8 _) (by omega) (fun o2 h2 => ?_)
    refine top_fields h2 (len_lit8 _) (by omega) (fun o3 h3 => ?_)
    refine top_fields h3 (len_one _) (by omega) (fun o4 h4 => ?_)
    refine top_push h4 (by omega) (fun o5 h5 => ?_)
    refine top_fields h5 (len_lit8 _) (by omega) (fun o6 h6 => ?_)
    refine top_push h6 (by omega) (fun o7 h7 => ?_)
    refine top_fields h7 (len_one _) (by omega) (fun o8 h8 => ?_)
    refine top_extend h8 (len_lit8 _) (by omega) (fun o9 h9 => ?_)
    refine top_frontier h9 (by omega) (fun o10 h10 => ?_)
    refine top_fields h10 (len_lit8 _) (by omega) (fun o11 h11 => ?_)
    refine top_frontier h11 (by omega) (fun o12 h12 => ?_)
    exact ⟨_, rfl, fun v hv => by cases hv; omega⟩

/-- Totality and output length for the GATE constant: on every input the gate returns `ok`
    (never `fail`/`div`, i.e. the modelled Rust body never panics), and an `Ok v` result has
    exactly `expected_len self` bytes. -/
theorem gate_total_length (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    ∃ r, pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes self = ok r ∧
      ∀ v, r = core.result.Result.Ok v → v.val.length = expected_len self := by
  rw [gate_eq]; exact ref_public_bytes_good self

end NPL_PublicBytes

#print axioms NPL_PublicBytes.P_eq
#print axioms NPL_PublicBytes.private_public_eq
#print axioms NPL_PublicBytes.withdrawal_public_eq
#print axioms NPL_PublicBytes.semantic_eq
#print axioms NPL_PublicBytes.fields_loop_body_eq
#print axioms NPL_PublicBytes.fields_loop_eq
#print axioms NPL_PublicBytes.fields_eq
#print axioms NPL_PublicBytes.frontier_eq
#print axioms NPL_PublicBytes.gate_eq
#print axioms NPL_PublicBytes.gate_total_length
'''

(E / 'NPL_PublicBytesRef.lean').write_text(REF)
def indent_first(txt):
    out=[];k=None
    for line in txt.split('\n'):
        ind=len(line)-len(line.lstrip(' '));s=line.strip()
        if k is not None:
            if (ind==k and s.startswith('|')) or ind>k:
                out.append('  '+line);continue
            k=None
        out.append(line)
        if s=='first' or s.endswith(' first'):k=ind
    return '\n'.join(out)

(E / 'NPL_PublicBytes.lean').write_text(indent_first(PROOF))
print('written')
