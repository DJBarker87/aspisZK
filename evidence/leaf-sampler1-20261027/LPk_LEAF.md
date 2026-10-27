# LPk low_base_p_digits native P6 bridge

**CLOSED — one opaque-leaf bridge under narrowed D188. No headline premise
removed.** S2 and the deployed 100-bit security target remain not established.

For every native `[u8;32]` block, porting its bytes and returned u32 values by
their natural values gives
`AspisR1Post25Sampler.sampler.low_base_p_digits block = ok (nativeDigits,nativeQuotient)`.
The digits are the low eight base-P digits of the 256-bit little-endian value;
the remaining quotient is at most 256. All limbs, all bytes, and all eight
ordered state transitions are included. No canonical-limb restriction or
whole-function equality is assumed.

This is the approved hybrid native/Kani/Lean P6 argument. The exported Lean
carrier theorem `LPk_Result.native_result` takes an explicit local relational
trace. The universal native gates and exact source association below construct
that trace for the frozen function; it is not an independently assumed native
accepted run or a supplied whole-output equality. This is not a claim that Lean
itself elaborates Rust, nor a new source-to-ELF theorem.

## Pins and scope

- Frozen Rust: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`,
  `crates/aspis-r1-cost-probe/src/sampler.rs:56`, SHA256
  `d7bd77dd4956e262cc21c381ec7eb5e855106375ed71326287d8fadf756425d0`.
- Cohort: `AspisR1Post25Sampler.Funs`, ordinary-sample candidate sanitized
  Funs SHA256 `f02a8fc4503304c2630052a116be257ef507780ffe166844e1b08d71e0e9ec11`.
  Existing coherent SInt2 objects and their pinned source selection are reused
  read-only; no missing Lean dependency rebuild was necessary.
- Frozen Cargo.lock SHA256
  `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
  Every actual Kani run has a fresh package/edge graph audit, offline execution,
  and matching before/after lock hashes. No cfg-if/libc drift is admitted.
- Kani 0.67.0 and tool binary hashes: `LPk_TOOLCHAIN.log`.
  Lean 4.32.0 binary/dependency fingerprints are in the per-attempt receipts.
- `LPk_SOURCE.json` checks 1,234 frozen scratch files, the exact factored native
  step expressions, byte decoder and traversal/store sequence. The sole frozen
  file difference is a cfg(kani) module declaration in the scratch sampler;
  the added module is retained only as `LPk_harness.patch` and per-run patches.
  Repository crates/ and programs/ are unchanged.

The defective raw emission remains defective and untouched. This packet supplies
the native opaque-leaf route; it does not restore that body's translation credit
or repair its dropped restoration callback. The installed headline remains
`AspisR1.RPx_Deployed.deployed`; L154 remains its statement parameter.

## Checked bridge

| Stage | Accepted evidence | Exact obligation |
|---|---|---|
| Cohort step | L003/L004: `LPk_Step.unique/machine_step/step_join`, `LPk_Cohort.step_result` | Successful cohort Result writes q; q*P+r=rem*2^32+limb, r<P; relation uniquely identifies the model step. |
| Native arithmetic | K008, K009, K020; L012 `LPk_Constant.*` | Uncast quotient fits u32; remainder<P; native div/rem satisfy full reconstruction. K020 uses `(q<<31)-q`; Lean proves this is q*P and proves shift, subtraction and sum do not wrap. |
| Native traversal | K012/K013 | Arbitrary eight-limb array; high-to-low order, all quotient writes retained, remainder capture threaded. Each step uses the paired relation stub. |
| Byte/scalar carriers | K014; L014 `LPk_Casts.*`; inherited byte-word laws | Exact frozen little-endian decoder; pack by shift/or equals multiply-add; quotient and digit casts retain natural values. |
| Composition | L006/L008: `LPk_Induction.*`, `LPk_Result.native_result` | Induction over limbs and eight passes; same digit array, full quotient-array interpretation and returned low limb; complete cohort Result. |
| Return checks | L013 `LPk_ReturnChecks.checks` | All seven upper quotient limbs are zero and low quotient is at most 256, derived from the same trace. This also accounts for the source debug assertions. |
| from_fn wrapper | K011 | Exactly eight calls in index order; arbitrary whole-state transitions share the mutable quotient; each output is stored at its index and final capture is retained. |
| Non-vacuity | Reused SDX_R003 and SDX_L032/L033, pinned in LPk_REUSED.json | Native/cohort Results agree for zero, P, P+1 and 32 ff. No fixture replay is claimed. |

`LPk_STUBS.md` names the stub, cohort theorem, native step discharge, scalar
ports and complete domain. The initial remainder is zero; K009 and each paired
stub return establish rem<P for every subsequent caller. Limb inputs range over
all u32 values. All local gates are universal on these domains, so order and
writeback apply to the same native execution. `LPk_Step.unique` prevents choosing
different compatible step outputs in the native/model association.

The source-shaped owned trace uses `SamplerBytePass.digits` in high-to-low
order, `LPk_Induction.Pass` for each retained quotient array, and
`LPk_Induction.Digits` for the eight mutable callbacks. The scalar ports identify
native words with Aeneas U32/U64 by value; `values_injective` identifies entire
digit carriers. `LPk_Result.low_word` identifies the actual `quotient[0]` return.
There is no digest/oracle operation in this leaf.

## Failed attempts retained and replaced

- K001: metadata-only missing scratch dependency, no Kani launch.
- K002/K003: missing unchanged include files; copied from the frozen revision.
  K004: scratch module path error; fixed without changing the frozen body.
- K005 combined step, K006 combined traversal, K010 widened reconstruction,
  K015 wrapping reconstruction, K017–K019 higher 16-bit projections: timed out
  at the unchanged 90-second harness limit. No cap or timeout was raised.
- K008/K009 split the two native bounds; K012/K013 split traversal and use a
  wide relation to avoid specification-only u64 overflow checks. K020 replaces
  the failed multiplier shapes with the sparse constant law. K016's passing
  low-16-bit projection is retained but is not used as full reconstruction.
- K007: memcmp unwind failure. K011 replaces array comparisons with universal
  arbitrary-coordinate comparisons, keeping the same complete state claim.
- L001/L002/L005/L007: rejected rewrite/projection errors; fixed sources compile
  in L003/L006/L008. Failed sorryAx diagnostic prints are excluded evidence.

The initially considered middle-byte projection was not run: the sparse
constant rewrite supplied the full relation instead. Own scripts were repaired
only for scratch dependency/path handling and equivalent pointwise validation;
shared admission, launcher, monitor, shim and coherent workspace were untouched.

## Final validation and retained boundaries

L015 is the single final axioms audit: all 26 new theorem prints contain only
propext, Classical.choice and Quot.sound, or a subset. Exit 0, wall
1.567730025 s, peak RSS 3,838,636 KiB, swap 0, source revision `9941184f39`;
exact source/dependency hashes and full lines are in its receipt/stdout.
K020: exit 0, wall 9.137236032 s, peak RSS 330,168 KiB, swap 0; all 15 checks
passed (one unreachable). Every attempt has exact target/command, source
revision/hash, dependency fingerprint, exit, wall, RSS, swap and axioms/N/A.

Budget used: **15/60 Lean attempts** (11 pass, 4 rejected proof errors),
**19/20 actual Kani runs** (8 pass, 3 compile failures, 1 unwind failure,
7 timeouts), plus one metadata-only preflight. Conservatively twenty Kani
attempt identifiers were consumed. No memory kill or unchanged timed-out rerun.
Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Lean used -M7000, Rust/Kani compilation was optimized. One scope at a time;
every admission required allowed=true AND exit 0. No admission refusal occurred.
Peak attempt RSS 3,869,312 KiB; swaps zero throughout. `LPk_VERIFICATION.json`
contains the full ledger, aggregate wall 725.502372980 s, source and scope checks.

The compiler/platform/library/P6 association trust and standard logical axioms
are retained. No cryptographic assumption, security game, metric, failure event,
headline quantifier, or runtime trust item is added, changed or discharged.
No session A worktree/candidate, other worker prefix, or wallet key was touched.

No frozen-manifest, adversarial/runtime suite or SBF rebuild was run: their
covered source/artifacts did not change. The three ELF pins are **inherited,
not freshly reproduced**: default
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
Owned host caches and solver scratch are removed after receipt collection;
`LPk_CLEANUP.json` records hashes and sizes. No binaries are committed.
All stage commits are local; no push or merge.

This closes exactly sampler::low_base_p_digits as one opaque leaf. It removes
no top-theorem premise and does not close enclosing A2, S2, other opaque leaves,
D188 audits, runtime/oracle joins or source-to-ELF correspondence.
