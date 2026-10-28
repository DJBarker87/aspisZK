# Decoder and native helper resume — D417

**Target not yet established. Whole ledger rows removed: 0.**

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-rjdec`, branch
`codex/pv-rjdec-20261028`, resume entry `b31649ce7ff391eb76d97011525bf97de2a26d48`.
The preceding report and original receipts remain in `REPORT-before-D417.md`.
All newly created Lean source modules use `R1Z.PV_RJDec_`. Existing RunJoin
sources were neither edited nor rebuilt with changes. No shipped Rust, other
worktree, wallet, account key, endpoint, observer or simulator was changed.

## Restored V221/V222 law actually consumed

The prior source/LLVM diagnostic remains valid about its original model, but
**its compiler-fence mismatch is no longer a stop for this work**. The merged
`PV_RDCD_ZeroWorld`, `ZeroSelected`, `ZeroConsumed`, `ZeroDrop`, `ZeroTrace` and
`ZeroCompatibility` sources were read, pinned at this branch's HEAD and built
privately against the verified inherited cohort. Their original row records
say RESTORED, class C, structural (K-1 substitute), not whole-native-runtime
or privacy closure.

Before, each byte step was `volatileWrite(address, 0); compilerFence(SeqCst)`.
After, each byte step is `volatileWrite(address, 0); asmReadBarrier(address)`:
zeroize 1.9.0's explicit volatile write followed by its x86_64 readonly inline
assembly optimization barrier. `PV_RDCD_ZeroWorld.source_reference` proves
`native (base+i) n w = indexed base i n w`; `ZeroConsumed.emitted_execution`
passes both the complete zero value and that indexed post-world to any Result
continuation. `ZeroDrop.complete` consumes the byte array and returns Unit and
that post-world. Exact ordered history, overwrite, outside-memory/frame and
allocator counter laws are retained. No hardware-fence equality is asserted.

The restored selector installs op122/op123, not op130. The reached
`PV_W_R_ReserveBuild` thunk is precisely op130, `Zeroizing.zeroize`, with the
32-byte emitted dictionary. The deployed 1.9.0 wrapper's complete body is
`self.0.zeroize();`, exactly one delegation. `wrapper-source-binding.json`
retains its source hash and rejects omitted, duplicated and extra-call
controls. Its primitive byte semantics are the restored V221/V222 law; this
is not a new native differential or a compiler proof.

PROVED lower association: `PV_RJDec_ZeroizingSelected.wrapper` installs that
one delegate and proves its complete Result is `.ok (Array.repeat N 0#u8)`.
`PV_RJDec_ReachedZero.complete` identifies the exact reached 32-byte thunk's
outcome with the typed handler and commits the restored indexed post-world,
retaining `[(w,none)]`. `PV_RJDec_AsmBind.complete` keeps arbitrary subsequent
success, failure or divergence, post-world and ordered calls.

`PV_RJDec_ReserveBuild.erase_program`, `MaskedWithAttempt.erase_program`,
`Entry.erase_program` and `Runtime.source` propagate the typed zero-array call
through the actual reified prover caller tree. Their complete source Result
equalities use the explicit selected dictionary. Every other source branch,
error and continuation stays present. This is new reference reification,
not a modification of Rust or the original `PV_W_` / `PV_RunJoin_` programs.

## (a) Both native ROMView laws — OPEN

Neither law has been supplied to `CommonSample32.complete_view` or
`CommonObserver32.complete_pair`. Their exact unchanged all-Result obligations
are, for every adversary, statement and outer Result `out`:

```text
a.disclosed adv x out = b.disclosed adv x (mapR (fun p => (p.1, project p.2)) out)
a.observerOracle adv x out =
  b.observerOracle adv x (mapR (fun p => (p.1, project p.2)) out)
```

`PV_RunJoin_Deployed.Runtime` still takes both fields as arbitrary data. No
native implementation/installation of either field is established here.
Their complete-observation factorization also remains unproved: source
failure and divergence erase post-world and calls in the Result-only carrier;
even success omits the call prefix. The original `Factor.exists_iff`,
`ResultCases.fibres_iff` and pair criterion name the necessary reachable-run
facts. In addition, Common's hypotheses quantify over **all** Results, so a
reachable-run factorization alone does not prove its fixed decoders' total
extension laws. No rejected suffix, failure signal, oracle event, divergence
prefix or side-channel observation has been discarded to obtain equality.

New lower parser work is recorded in `parser-reification.json`,
`recursive-parsers.json` and `chunked-parsers.json`. These reify pinned EJR
**emitted input parser/validator bodies**, preserving every original length,
header, transition, canonicality, binding and validation branch, both Result
layers, outer failure and divergence. They support input identification and
rejection-path work; they are not native ROMView decoders or proof-publication
serialization laws. Native primitive/helper adequacy remains explicit.

The final accepted parser inventory and exact statements are in the resume
audits and receipts. The unchunked snapshot candidate failed on default
recursion depth; named digest-continuation chunks replace it. No proof limit
was raised and no unchanged failure was rerun. Staged/uncompiled candidates
are explicitly excluded in `resume-uncredited-sources.json`.

## (b) Installed native helper effects — OPEN

PROVED interpreter construction: `PV_RJDec_MemoryInstalled.array_complete`
returns the selected emitted op130 result, the committed
`PV_RDCD_ZeroWorld.indexed` post-world and exactly `[(w,none)]`.
`MemoryInstalled.reserve` and `.drop` retain the previously checked complete
reserve/drop interpreters; `.base_unchanged` preserves the original base
helper/file handler algebra. `PV_RJDec_Runtime.executes` gives the complete
operational execution judgment for the reified entry with this installation.
No world or prefix is removed on a rejected or divergent continuation.

The actual native memory metadata, addresses, view/commit maps, allocation
and free semantics, remaining base helper routing and OS/Drop/unwind effects
are not identified by those construction theorems. The original interpreter's
op130 is still an opaque base helper. The new reification gives that reached
call an explicit typed handler and proves its source Result association;
full native routing/effect equivalence to the original runtime remains P.
No native purity, heap identification, OS silence or assembly/compiler-fence
identity was added as an assumption or trust field.

## (c) Parked V047 native handle/decoder identification — OPEN

The original exact mathematical theorem remains
`AspisR1.PV_2TNV_HeadlineFibre.fibre handle`:
`∃ w : H.Instance, H.public w = (PV_2TNV_PublicEncoding.x handle).1`, where
`H := PhaseWireLog2Bin.honest PrivacyR1HeadlineDeployedReal.input`.
It constructs the transfer-13 witness; runjoin's index-zero fixture does not
match it. The native handle and actual statement equality remain unproved.

PROVED exact transport consumer: `R1Z.PV_RJDec_V047.consume encoded actual
fibre native_identification`, with premises
`fibre : ∃ w : H.Instance, H.public w = encoded.1` and
`native_identification : actual = encoded`, concludes
`∃ w : H.Instance, H.public w = actual.1`.
Instantiate `encoded := PV_2TNV_PublicEncoding.x native_handle` and pass the
original `HeadlineFibre.fibre native_handle`. The missing premise is still
the **actual** native statement/handle/decoder identification, not a ROMView
equality. The consumer proves no native handle construction or wrapper run.
The explicit `FixturePdaRuntime base` and joint proof binders remain required
by the parked joint implication; they were not discharged or added to T.

An additional direct-import cohort gap is recorded in `v047-source-gap.json`:
`PV_2TNV_ByteEncoding` imports `JHb_DataRequest`, whose historical pinned source
is absent at this merged HEAD. It was read through its exact committed pin;
no replacement source or object was invented. That gap is distinct from the
substantive native identification obligation.

## Endpoint and deployment boundaries

Premises removed/added/weakened/changed: **0/0/0/0**. V038, V045, V163, V165,
V167 and V244 remain. All eight `PV_RunJoin_Premises` fields and the exact
three TrustItems (`entropy_law`, `entropy_kernel`, `observation`) are retained.
The coupling, bad/query events, failure-independence requirement and complete
observer/simulator are unchanged. `endpoint-boundaries-unchanged.json` and
`stage-A-source-identity.json` record exact before/after source checks.
Historical three-ELF evidence is reused only for the empty frozen Rust/client
diff from 82566acdfb. Compiler-cohort, D188, K-1/K-2 and L1/L2/L3 boundaries
retain their prior scope. No native correspondence is inferred from finite
validation, source reification or a cached axioms audit.

## Validation and final accounting

Final statements, axioms, focused replay, exact resource metrics and attempt
accounting are appended after the last scopes complete. Every accepted source
and object must match its committed pin and dependency fingerprint. Only
standard axioms are permitted. No native scope or Kani run was added in this
resume, and no key/account file was touched.
