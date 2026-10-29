# Deployed static dispatch and retained installation models

Read-only source audit at candidate `60a288b5461129634a3714d56756a1c64fdca7e4`.
Runjoin sources were read using `git show origin/codex/pv-runjoin-20261026:<path>`;
its worktree, branch and objects were not changed or imported by this audit.

The route is `devnet_spend::main -> plan::run -> plan::prove ->
RealR1_client::prove_for_proof_accounts -> prover::prove_masked_retrying_with`.
The client supplies `statement.semantic_public()`, `&compiled`, `HOST_HASH`, the
mutable durable nonce store and `|k| accounts.nonce(k)`. Neither source-level
`ExternalFuns` records nor arbitrary encoder/powers function pointers are passed:
the extraction dictionaries model static Rust calls.

At `prover.rs:354`, `opening_claim_bytes` calls
`aspis_core::r0::encoder::eval_message::<WideExact>(&coefficients[lane], z1)`.
At `prover.rs:360`, `opening_batch` calls
`crate::prover_powers::powers::<29>(gamma)`. `E` is the `WideExact` alias in
`prover.rs:3`.

## op79

`PV_DL_EncoderNative.value` retains the native basis-then-forward-chunks/zip
loop, both ZERO initializations, ordered mul/add for each pair, and final
`p0 + y*p1`, as a complete Result. Existing `PV_DL_EncoderNative.source_reference`
and `PV_DL_EncoderControl.source_reference` identify it with the owned reference
and installed control respectively. Draft `lean/PV_RJ4ID_Op79.lean` composes
these equations and identifies the complete dictionary update with
`PV_DL_EncoderSelected.selected`. This draft is uncompiled until its own receipt
exists; its definition does not establish a deployed association on its own.

Runjoin's `ClaimEvaluator48.complete` / `ClaimEvaluation49.complete` consume
exactly `PV_DL_EncoderSelected.selected ops`. Their source specialization is
independent of the backend-message association in step (2).

Existing source binding: `evidence/pv-dlib-20261028/encoder-native-shapes.json`
pins all four application bodies (eval_pair, eval_message, values, double),
the whole owned encoder, and six differences with named Lean transport lemmas.
It explicitly leaves standard forward slice chunks/zip semantics implicit.
Its native check used nightly-2026-06-01 and M31/QM31, not deployed rustc1.94.1
and the actual WideExact specialization. Hence that execution alone supplies no
new deployed-configuration native validation under (x)/(x'). Under own-1 a
current binding must cover the complete deployed forward iterator cone,
index guards, stores and drop/error/abort steps, including rust-src1.94.1.
V370 and the owner's D381/D386 compiler boundary remain retained. No input-free
rule applies: the encoder consumes a witness-derived message and point.

## op254

Runjoin combines encoder installation with
`PV_RunJoin_GammaPowers44.inputs ops`, whose op254 is
`ProverRwP6PowersInstall.powers ops`. `EncoderGammaFields49.incoming_powers`
proves encoder installation preserves it. `EncoderGammaFields49.powers` proves
the later weight/body dictionary also preserves the incoming op254.

The latter retained powers source is the historical `weights::powers` early
return model, whereas current deployed static dispatch reaches the prover-local
indexed copy in `prover_powers.rs`. Current copy initializes ZERO array and ONE,
stores out[i], increments i, multiplies p by x only when i<N, and returns out.
The historical model early-returns at the final index instead of making the
last no-op loop test. No large recurrence should be reduced to prove equality.

`PV_B1_PowersBridge.op254_copy_equal_original` already proves this exact control
difference, all Usize N and arbitrary raw WideExact inputs, by finite induction
including every Result branch. Its carrier is `PV_B1_254`, while runjoin uses
`ProverRwFull`. `ProverRwP6PowersNativeCaller.exact_result` separately transports
the runjoin callback to `AspisR1ProducerRelease47.power_fill` when a U8 counter
represents N (the deployed case is 29). No existing theorem directly equating
the PV_B1 deployed-copy carrier with the runjoin installed callback was found.
A new carrier/primitive transport, or an identical symbolic finite-induction
proof in ProverRwFull, is still required. The historical batch1 native/extraction
receipts predate (x); body/configuration parity and a 1.94.1 deployed check must
be established before crediting them at the deployed caller.

This map records proof design and source inspection; it claims no new deployed
installation, endpoint premise removal, native differential, or compiled theorem.

## Later deployed audit superseding the historical execution gap

`evidence/pv-rdcd-20261028/REPORT.md` and `rows/V201.md` explicitly classify
V201 as **SUSPENDED / D**. The exact original four-body/owned encoder checker
was recovered and passes, and `native-encoder/receipt.json` records deployed
release1.94.1 finite validation. The remaining blocker is **145 unresolved
concretely instantiated ChunksExact/Zip/array-iterator/index records** in the
conservative envelope (`rows/V201.json`). This is the exact unresolved own-1
source cone; finite comparisons do not prove its universal library transport.
The historical dlib toolchain gap above must not obscure this newer evidence:
the later native check can be reused at its finite-validation evidence class
if all relevant source hashes match, while the 145-record blocker remains.

## New symbolic op254 transport draft

The carrier gap above is now addressed by three **uncompiled drafts**, pending
fresh receipts: `PV_RJ4ID_PowersControl` defines the indexed deployed-copy
loop in `ProverRwFull` carriers, `PV_RJ4ID_PowersBridge.complete` proves its full
Result equals `ProverRwP6PowersSource.weights.powers` for every Usize N and
arbitrary original field callbacks, and `PV_RJ4ID_Op254.entry` specializes this
to the exact primitive dictionary captured by
`ProverRwP6PowersInstall.powers ops`. `Op254.installation` identifies the full
incoming record update (other fields preserved), definitionally the incoming
powers dictionary used by `PV_RunJoin_GammaPowers44.inputs`.

The proof follows existing `PV_B1_PowersBridge`'s symbolic finite induction,
without importing its different carrier or reducing a concrete recurrence.
The named decreasing invariant is `i.val + fuel = N.val`; the final store is
retained, no multiplication occurs after the last store, and fail/div Results
are matched at every indexed read and multiplication. Native source/primitive
association, source-to-machine-code V370, and observation effects remain
separate evidence obligations. These drafts are never proof credit by source
inspection alone.
