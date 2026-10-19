import AspisR1TerminalDecoder.Funs

/-! Invert the unchanged outer ASF8 decoder. Inner decoders and the terminal
validator are not unfolded. This proves a property of the actual emitted
functions, not Rust/runtime preservation or account authentication. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1TerminalDecoder.DecoderSuccess
open pool_v1.pair_forest_terminal

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem guard_success {α ε : Type} (b : Bool) (e : ε)
    (k : Result (core.result.Result α ε)) (v : α)
    (h : (if b then ok (.Err e) else k) = ok (.Ok v)) :
    b = false ∧ k = ok (.Ok v) := by
  cases b with
  | false => exact ⟨rfl, by simpa only [Bool.false_eq_true, ↓reduceIte] using h⟩
  | true => simp only [↓reduceIte] at h; cases h

private theorem add_exact (a b c : Usize) (hc : c.val = a.val + b.val) :
    a + b = ok c := by
  obtain ⟨z, hz, hval⟩ := spec_imp_exists
    (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  have he : z = c := by scalar_tac
  simpa only [he] using hz

/-- Only the finite source constant sum: 144 + (32 + 800 + (8 + 680)) + 216. -/
theorem statement_bytes : POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = ok 1880#usize := by
  unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  have h1 : (32#usize : Usize) + 800#usize = ok 832#usize := add_exact _ _ _ (by scalar_tac)
  have h2 : (8#usize : Usize) + 680#usize = ok 688#usize := add_exact _ _ _ (by scalar_tac)
  have h3 : (832#usize : Usize) + 688#usize = ok 1520#usize := add_exact _ _ _ (by scalar_tac)
  have h4 : (144#usize : Usize) + 1520#usize = ok 1664#usize := add_exact _ _ _ (by scalar_tac)
  have h5 : (1664#usize : Usize) + 216#usize = ok 1880#usize := add_exact _ _ _ (by scalar_tac)
  simp only [h1, h2, h3, h4, h5, bind_tc_ok]

private theorem terminal_tail_success
    (value out : PoolV1PairForestTerminalStatementV1)
    (h : (do
      let r ← validate_pool_v1_pair_forest_terminal_statement_v1 value
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok value)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          PoolV1PairForestTerminalStatementV1
          (core.convert.FromSame PoolV1PairForestTerminalFormatErrorV1) residual) =
      ok (.Ok out)) :
    validate_pool_v1_pair_forest_terminal_statement_v1 out = ok (.Ok ()) := by
  obtain ⟨r, hvalid, h⟩ := bind_success
    (validate_pool_v1_pair_forest_terminal_statement_v1 value) _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok u =>
    cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    have heq : value = out := by
      simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using h
    simpa only [heq] using hvalid

/-- Successful actual decoding validates exactly its returned object. All
outer header witnesses are reads/comparisons on the same original bytes. -/
theorem decode_success (bytes : Slice U8) (out : PoolV1PairForestTerminalStatementV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bytes = ok (.Ok out)) :
    validate_pool_v1_pair_forest_terminal_statement_v1 out = ok (.Ok ()) ∧
    bytes.val.length = 1880 ∧
    Slice.index_usize bytes 4#usize = ok POOL_V1_PAIR_FOREST_TERMINAL_VERSION ∧
    Slice.index_usize bytes 6#usize = ok pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION ∧
    (∃ magic expected : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        bytes { «end» := 4#usize } = ok magic ∧
      core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
        { start := 0#usize, «end» := 4#usize } = ok expected ∧
      core.cmp.PartialEq.ne.trait_default
        (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) magic expected = ok false) ∧
    (∃ tag : U8, ∃ kind : pool_v1.historical_anchor.PoolV1TransitionKind,
      Slice.index_usize bytes 5#usize = ok tag ∧ transition_kind tag = ok (.Ok kind)) := by
  unfold decode_pool_v1_pair_forest_terminal_statement_v1 at h
  simp only [statement_bytes, bind_tc_ok] at h
  have hlen := (guard_success (Slice.len bytes != 1880#usize)
    PoolV1PairForestTerminalFormatErrorV1.WrongLength _ out h).1
  simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
  have hlen' : Slice.len bytes = 1880#usize := by simpa using hlen
  have hlength : bytes.val.length = 1880 := by
    have hv := congrArg UScalar.val hlen'
    simpa using hv
  obtain ⟨magic, hmagic, h⟩ := bind_success
    (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bytes { «end» := 4#usize }) _ _ h
  obtain ⟨expected, hexpected, h⟩ := bind_success
    (core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
      { start := 0#usize, «end» := 4#usize }) _ _ h
  obtain ⟨b, hb, h⟩ := bind_success
    (core.cmp.PartialEq.ne.trait_default
      (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) magic expected) _ _ h
  have hbfalse := (guard_success b
    PoolV1PairForestTerminalFormatErrorV1.WrongMagic _ out h).1
  simp only [hbfalse, Bool.false_eq_true, ↓reduceIte] at h
  subst b
  obtain ⟨version, hversion, h⟩ := bind_success (Slice.index_usize bytes 4#usize) _ _ h
  have hversioneq := (guard_success (version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION)
    PoolV1PairForestTerminalFormatErrorV1.WrongVersion _ out h).1
  simp only [hversioneq, Bool.false_eq_true, ↓reduceIte] at h
  have hversion' : version = POOL_V1_PAIR_FOREST_TERMINAL_VERSION := by simpa using hversioneq
  subst version
  obtain ⟨tag, htag, h⟩ := bind_success (Slice.index_usize bytes 5#usize) _ _ h
  obtain ⟨r, hkind, h⟩ := bind_success (transition_kind tag) _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok kind =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨encoding, hencoding, h⟩ := bind_success (Slice.index_usize bytes 6#usize) _ _ h
    have hencodingeq := (guard_success (encoding != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION)
      PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding _ out h).1
    simp only [hencodingeq, Bool.false_eq_true, ↓reduceIte] at h
    have hencoding' : encoding = pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION := by
      simpa using hencodingeq
    subst encoding
    refine ⟨?_, hlength, hversion, hencoding,
      ⟨magic, expected, hmagic, hexpected, hb⟩, ⟨tag, kind, htag, hkind⟩⟩
    obtain ⟨r, _, h⟩ := bind_success (decode_terminal_common_boxed_v1 bytes) _ _ h
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok common =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      cases kind with
      | PrivateTransfer =>
        obtain ⟨offset, _, h⟩ := bind_success PAYMENT_STATEMENT_OFFSET _ _ h
        obtain ⟨payment, _, h⟩ := bind_success
          (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
            bytes { start := offset }) _ _ h
        obtain ⟨r, _, h⟩ := bind_success (decode_transfer_statement_boxed_v1 common payment) _ _ h
        cases r with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          exact terminal_tail_success value out h
      | Withdrawal =>
        obtain ⟨offset, _, h⟩ := bind_success PAYMENT_STATEMENT_OFFSET _ _ h
        obtain ⟨payment, _, h⟩ := bind_success
          (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
            bytes { start := offset }) _ _ h
        obtain ⟨r, _, h⟩ := bind_success (decode_withdrawal_statement_boxed_v1 common payment) _ _ h
        cases r with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          exact terminal_tail_success value out h

theorem decode_success_validated (bytes : Slice U8)
    (out : PoolV1PairForestTerminalStatementV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bytes = ok (.Ok out)) :
    validate_pool_v1_pair_forest_terminal_statement_v1 out = ok (.Ok ()) :=
  (decode_success bytes out h).1

#print axioms statement_bytes
#print axioms decode_success
#print axioms decode_success_validated
end AspisR1TerminalDecoder.DecoderSuccess
