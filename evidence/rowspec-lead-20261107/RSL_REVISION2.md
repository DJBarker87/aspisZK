# RSL Revision 2: allocation arms omitted from Revision 1

Target not yet established. This revision changes specifications only. No row is closed by it, and no proof that any frozen function satisfies its RowSpec was attempted.

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (unchanged). The trust rows, runtime assumptions, security metric and own-input domains are unchanged. Every change below adds an abort arm that the frozen code really has, at a named allocation site, under ruling (bl)(3): the abort carries only the event prefix. No generic "may abort" clause was added.

## 1. What was wrong in Revision 1

The NMT_ job reported two omissions in RowSpec_345 (evidence/tx1-owned-20261111/NMT_SPEC_FINDINGS.md). An audit of all 18 RowSpecs found the same two shapes elsewhere, plus a third.

- **NMT-S1: cloning a String-carrying error.** `OwnedAccount::data` returns `Err(error.clone())` and `data_len` returns `self.length.clone()` (r1_pool_adapter_owned.rs:21-24). solana-program-error 2.2.2 derives `Clone` for `ProgramError`, whose `BorshIoError(String)` clone calls `String::clone`, then `Vec::clone`, then `[u8]::to_vec_in`. That allocates when the String is nonempty and allocates nothing when it is empty. Revision 1 modelled both getters, and `require_verifier_checkpoint` which calls `data_len()?`, as pure `Except` values. Since the TX1:345, TX2:242, TX2:233 and TX2:234 domains are `True`, and TX2:241's (D1) does not constrain errors, these specs omitted a real abort.
- **NMT-S2: allocation before a later Err, inside a decoder modelled as `Option`.** `decode_public_statement_box` (r1_pool_adapter.rs:237) calls `decode_pool_v1_pair_forest_terminal_statement_v1`. That decoder reaches Box::new sites before its payment-decoder and validator Err arms: pair_tree_profile.rs:665/675/742 and pair_forest_terminal.rs:351/379/394. Revision 1's `S1Lib.decodeStatement : Bytes → Option Statement`, followed by one post-success `alloc`, could not abort on a rejecting run.
- **New in the audit (same shape as S2): the `format!` allocation in `lib.rs::error`.** `fn error(e) { msg!("r1:error:{:?}", e); InvalidInstructionData }` expands to `sol_log(&format!(..))`. The format string has a nonempty first piece, so `format!` allocates its String before the log line is written. Revision 1's `mapVErr` in TX1:328 and TX2:241 emitted the log line with no allocation site in front of it.

The audit also checked these sites and found no omission:
- the other `Option`-modelled children: the request, master, checkpoint, registry and entry decoders; `outputLane`; `validatePolicy`; `validateStatement`; `encodeCandidate`. None has a heap allocation in the frozen source. The master and checkpoint decoders allocate only in the outer Box, after the decoder returns, and that Box is already in `decodeMasterBox`/`decodeCheckpointBox`.
- TX2:217, whose only Box is the final one, after every check.
- `scan_proof_buffer` and `reconstruct_asq8_statement`. These are RS-valued PoolLib laws and carry their allocations inside.
- every `?` and `map_err(|_| ..)`. These move or drop the error and never clone it.
- `snapshot`'s `error.clone()`, which clones AccountBorrowFailed and has no heap payload.
- the verifier-crate error types (`verifier::Error`, `r1_wire::Error`, `CodecError`). All are `Copy`, with no String.
- the pure VLib getters (`validatedRecord`, `decodeK29`, `payload`). These are slices and arrays.

One comment was wrong, and only the comment changed. `PoolLib.encodeStatement` said "Vec allocation inside", but the frozen encoder returns `[u8; 1880]` by value. The comment now says so, so that no instantiation adds a spurious abort arm.

## 2. Choice for NMT-S1: abort arm, domain stays True

NMT proposed two fixes: an own-input snapshot-domain clause on 345, or the abort arm. I chose the abort arm, for these reasons:
- The ledger records no own-input clause for TX1:345. Its `explicit_child_domain_clauses` is empty, and NMT_CALLER_CLAUSES.json has `"TX1:345": []`. The same holds for 242, 233 and 234.
- The frozen getters behave in a definite way on every OwnedAccount: return the value, or allocate a clone and return it. That behaviour can be specified without narrowing the input set. A (bf)(2) clause would be a new restriction that the ledger obligation does not contain.
- The abort-arm fix applies uniformly to the five rows that share the getters, and it changes no domain. Changing domains would have moved four job targets' quantifiers.

The caller fact NMT asked to be checked is now proved in Lean. Every returning `snapshot` observation stores only AccountBorrowFailed in `length`, and only AccountBorrowFailed or InvalidAccountData in `bytes`:
- `RSL_TX1_344.snapshot_errs` proves this for one snapshot.
- `snapAll_errs` extends it to the snapshot array that both TX1:344 and TX2:240 build.
- `snapAll_getters_plain` concludes that at those caller occurrences `data = RS.ofExcept bytes` and `data_len = RS.ofExcept length`. So the new arms are unreachable at the only callers.

A worker proving 344 or 240 may use these lemmas to remove the arms. A worker proving 345, 242, 233, 234 or 241 must prove the arm from the emitted code under (bl)(3).

The restricted CLOSED packets that NMT lists for 335, 341 and 342 still apply only on their own domains. At a Domain-True row, the worker needs the unrestricted law, which is the transcription itself, or must discharge the packet domain internally.

## 3. Changed definitions in RSL_Base

The definitions below changed. The other additions to RSL_Base are support lemmas, with no change to any statement: `ofCloned_*`, `data_of_snapshotErrs`, `Spec.bind_two`, `RS.lift_alloc_iff`, `RS.alloc_seq_iff`, `RS.ofCloned_heap_abort`, `RS.ofCloned_plain_no_abort`, and `OwnedAccount.SnapshotErrs` (a definition used only by the lemmas).

Before:

    def OwnedAccount.data (a : OwnedAccount) : Except ProgramError Bytes := a.bytes
    def OwnedAccount.data_len (a : OwnedAccount) : Except ProgramError Nat := a.length
    def verifierCheckpoint (a) (program) (writable) : Except ProgramError Unit :=
      if meta-bad then .error .invalidAccountData
      else match a.data_len with
        | .error e => .error e
        | .ok n => if n != CHECKPOINT_BYTES then .error .invalidAccountData else .ok ()

After:

    def ProgramError.cloneAllocates : ProgramError → Bool
      | .borshIoError msg => !msg.isEmpty
      | _ => false
    def RS.ofCloned (x : Except ProgramError α) : RS α :=
      match x with
      | .ok a => RS.pure a
      | .error e => if e.cloneAllocates then RS.bind (RS.lift Spec.alloc) (fun _ => RS.throw e)
                    else RS.throw e
    def OwnedAccount.data (a : OwnedAccount) : RS Bytes := RS.ofCloned a.bytes
    def OwnedAccount.data_len (a : OwnedAccount) : RS Nat := RS.ofCloned a.length
    def verifierCheckpoint (a) (program) (writable) : RS Unit :=
      if meta-bad then RS.throw .invalidAccountData
      else RS.bind a.data_len fun n => RS.check (n != CHECKPOINT_BYTES) .invalidAccountData
    def Spec.allocIf (b : Bool) : Spec Unit := if b then alloc else Spec.pure ()

`RS.ofCloned_heap_abort` and `RS.ofCloned_plain_no_abort` show that the arm has force: it admits the silent abort exactly for a nonempty BorshIoError. A payload-free error still gives only its Err.

## 4. Changed RowSpecs, with before and after statements

Each `RowSpec_X` keeps its form, `∀ a env, Domain a → Ref a env (impl a env)`, and its Domain is unchanged. What changed is `Ref`. "Direct" means the module's own `Ref` text changed. "Inherited" means only an OPEN child `Ref` that it calls changed.

### TX1:345 stage1_owned (direct). Also: new S1Lib field

    structure S1Lib (V) where
      ...
    + decodeReachesAlloc : Bytes → Bool   -- reached ≥1 internal decoder Box site (CLOSED TX1:332)

    - RS.seq (RS.ofExcept (verifierCheckpoint ck a.program_id true)) <|
    - RS.bind (RS.ofExcept ck.data) fun checkpointData =>
    + RS.seq (verifierCheckpoint ck a.program_id true) <|
    + RS.bind ck.data fun checkpointData =>
      RS.seq (RS.ofExcept (requireZero checkpointData)) <|
    - RS.bind (RS.ofExcept pub.data) fun publicData =>
    + RS.bind pub.data fun publicData =>
    + RS.seq (RS.lift (Spec.allocIf (C.decodeReachesAlloc publicData))) <|
      RS.bind (RS.ofOption (C.decodeStatement publicData) .invalidAccountData) fun st =>
      RS.seq (RS.lift Spec.alloc) <|
      ...
    - RS.bind (RS.ofExcept p.data) fun proofData =>
    + RS.bind p.data fun proofData =>

The decoder emits no event, so its reached internal allocation sites collapse to one `allocIf` before its Result. Each such site either continues or aborts with the same prefix. This representation is exact, not an over-approximation:
- On an early-rejected input, `decodeReachesAlloc` is `false` and no abort is added.
- On a run that reaches a Box and is rejected later, the abort is admitted.

`decodeReachesAlloc` is a total function fixed by the frozen decoder. It has exactly one admissible instantiation, as with every other S1Lib field. The domain stays `True`. The row also inherits the TX1:328 change.

### TX1:328 first_decoded (direct)

    def mapVErr (V) (r) : RS Bytes := match r with
      | .ok b => RS.pure b
    - | .error e => RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debugV e))))
    -                 (RS.throw .invalidInstructionData)
    + | .error e => RS.seq (RS.lift Spec.alloc) <|
    +               RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debugV e))))
    +                 (RS.throw .invalidInstructionData)

**A Revision 1 strength claim is superseded.** Revision 1's `rejects_silent` rejected every event-free outcome at k ≠ 10, including the constant abort. That claim depended on the missing `format!` allocation:
- At k ≠ 10, tx1 returns Err(Parse) silently.
- The frozen `error` function can then abort at the `format!` allocation with an empty prefix.
- Under (bl)(3), the same holds after a heap::filled failure at k = 10.

So in the allocation-failure model the constant abort is a real behaviour of first_decoded. A faithful spec must admit it. This is a reporting and proof correction, not a protocol change: an abort writes nothing and accepts nothing.

Revision 2 replaces the theorem with two:
- `rejects_silentRet`, which rejects every event-free returning implementation, including every constant Err.
- `ref_admits_abort`, which records the admitted abort.

All other rows keep both rejection theorems unchanged.

### TX2:241 stage2_owned (direct, plus inherited from 242)

    - RS.bind (RS.ofExcept acc0.data) fun proofData =>
    + RS.bind acc0.data fun proofData =>
    - RS.bind (RS.ofExcept acc6.data) fun checkpointData =>
    + RS.bind acc6.data fun checkpointData =>
      mapVErr: the same `RS.seq (RS.lift Spec.alloc)` insertion as TX1:328

(D1) and (D2) are unchanged.

### TX2:242 validate_asq8 (direct, plus inherited from 233)

    - RS.bind (RS.ofExcept proofAccount.data) fun pdata =>
    + RS.bind proofAccount.data fun pdata =>

### TX2:233 authenticate_asq8_accounts (direct, plus inherited from 234)

    - RS.seq (RS.ofExcept (verifierCheckpoint v a.verifier_program false)) <|
    + RS.seq (verifierCheckpoint v a.verifier_program false) <|
    - RS.bind (RS.ofExcept m.data) fun mdata =>      + RS.bind m.data fun mdata =>
    - RS.bind (RS.ofExcept c.data) fun cdata =>      + RS.bind c.data fun cdata =>
    - RS.bind (RS.ofExcept l.data) fun ldata =>      + RS.bind l.data fun ldata =>

### TX2:234 authenticate_invariant_release_registry (direct)

In both `immutableBranch` and `v1Branch`:

    - RS.bind (RS.ofExcept a.registry_account.data) fun rdata =>
    + RS.bind a.registry_account.data fun rdata =>
    - RS.bind (RS.ofExcept a.entry_account.data) fun edata =>
    + RS.bind a.entry_account.data fun edata =>

The proof of `rejects_constErr` changed one rewrite, `RS.ofExcept_error` to `RS.ofCloned_error _ rfl`, because the AccountBorrowFailed witness has no heap payload. The theorem statement is unchanged.

### Inherited only (module text unchanged; the meaning changes through a child Ref)

- **TX1:344 stage1.** Through `TX1_345.Ref`. Its `S1Lib` parameter type gained a field. New support lemmas: `snapshot_errs`, `snapAll_errs`, `snapAll_getters_plain`.
- **TX1:333 and TX1:330.** Through TX1:344 and TX2:240.
- **TX2:240 stage2.** Through `TX2_241.Ref`.
- **TX2:221, RowSpec_221_full and TX2:213.** Through TX2:240. The stage1 packet is parametric.

### Unchanged (statement and meaning)

TX2:217, TX1:136, TX1:137, TX1:087 and TX1:094. Their Refs do not use the owned getters, `error`, or S1Lib, and their children are full-law `Child`/`VLib` packets.

## 5. Running jobs: does the current target change?

| Job | Rows | Target changed? | What to tell it |
|---|---|---|---|
| NMS_ | 241, 242 | **Yes, direct** | `data`/`data_len`/`verifierCheckpoint` are now RS-valued with the clone arm. 241's `mapVErr` has the `format!` alloc. Both inherit 233/234. |
| NMX_ | 233 | **Yes, direct** | Four getter or checkpoint sites, plus inherited 234. |
| NMO_ | 136 | No | none |
| NMP_ | 137, 087 | No | none |
| NMT_ | 345, 328, 094 | **345 and 328: yes. 094: no** | NMT-S1 is fixed by the arm, and the domain stays True. NMT-S2 is fixed by `S1Lib.decodeReachesAlloc`. 328 has the `format!` alloc, and `rejects_silent` is replaced by `rejects_silentRet` and `ref_admits_abort`. The NMT_RSL_TX1_345 copy must be rebased. |
| NMV_ | 344, 240 | **Yes, inherited only** | Own wrapper bodies unchanged. Child refs 345 and 241 changed. Use `snapAll_getters_plain` to remove the clone arms at the caller. |
| NNC_, NNE_, NNF_ | adapters | **Yes, if they mention any of the following** | `OwnedAccount.data`/`data_len`/`verifierCheckpoint` (type changed from `Except` to `RS`); `S1Lib` (new field); `TX1_328.mapVErr`, `TX2_241.mapVErr` or `TX1_328.rejects_silent`; or the Refs of 345/328/241/242/233/234 and their inheritors. Adapters stated only over the parametric packets recompile unchanged. TAS_Interfaces, TAS_Top and TCK_WeakRoot0 recompile unchanged. |

## 6. Validation run

- **RSL modules.** Clean replay on 2026-11-07 from 10:23:42Z, after all RSL `.olean` files were deleted. All 20 RSL modules ran one file at a time with `lake env lean -o`, in dependency order (rsl_compile.sh). Every exit status is 0. Total wall time is about 7 s. The largest peak RSS is 728,203,264 bytes (RSL_TX2_217), with 0 swaps. These are focused jobs far below 8 GiB, run on the development machine with no cgroup. Per-file figures: RSL_COMPILE_REV2.tsv.
- **Axioms.** RSL_Audit.lean compiled with exit 0. RSL_AUDIT_OUTPUT_REV2.txt shows that every rejection theorem and every Revision 2 lemma depends only on `propext` and/or `Quot.sound`. There is no `sorryAx`, no `Classical.choice` and no `native_decide`.
- **Top-level files.** `../top-assembly-20261107/tas_compile.sh` compiled TCK_WeakRoot0, TAS_Interfaces and TAS_Top with exit 0, with source files unchanged. Their printed axiom sets are the same as in TAS_AXIOMS_OUTPUT.txt.
- **Not run.** No host, Kani, extraction or combined-import run was made. The correspondence of `decodeReachesAlloc` to the emitted decoder, and of the clone arm to the emitted `Clone` call, is a worker obligation at the gate.
