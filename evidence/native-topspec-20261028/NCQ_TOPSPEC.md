# Composition medium: exact top specification

Status: design audit, 2026-10-28. No Kani run, no new trust adoption, no deployed closure claim. Ruling (w) supplies a useful place to compose Rust contracts; it does not make a Rust verdict a Lean proof. The medium can replace unchecked implementation assertions by audited contract evidence plus a smaller semantic interpretation boundary, conditionally on full coverage. It cannot unconditionally remove `extraction` from the present kernel statement.

## Audited boundary and carriers

The authoritative statement is `evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt` (its printed declaration is `AspisR1.FJv_Deployed.deployed`). Write `O` for exactly the installed `DrvC_Installation.sdk (FIp_Install.configuration indexError (IDa_Deployed.deployedConfiguration missing indexError reservation) reservation)` in that print. The checks below generalize over `ops`; specialize to this exact `O`, without replacing its installed callbacks by arbitrary stubs.

`native1` and `native2` are universally supplied Lean function values, not Rust symbols, foreign-function handles, extracted definitions, or proofs of association with an executable. Their types are:

```
Program  := AdapterRw.solana_pubkey.Pubkey
Accounts := Aeneas.Std.Slice AdapterRw.Cuts.Account
Slot     := Aeneas.Std.core.result.Result U64 AdapterRw.Cuts.PE
First    := Program → Accounts → Slice U8 →
            Aeneas.Std.Result (core.result.Result (alloc.vec.Vec U8) Cuts.PE)
Second   := Program → Accounts → Slice U8 → Slot →
            Aeneas.Std.Result (core.result.Result Unit Cuts.PE)
```

The outer result distinguishes `ok`, `fail error`, and `div`; the inner result distinguishes `Ok value` and `Err ProgramError`. Equality includes all constructor tags and payloads, including checkpoint bytes and error values. Neither `First` nor `Second` carries a heap, allocator state, runtime return-data buffer, or digest-call trace.

| Field | Exact obligation and domain |
| --- | --- |
| `stage1` | `∀ program accounts data, native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned O program accounts data`. All well-typed Lean arguments, including arbitrary account counts/contents/flags/keys, malformed instructions and rejected inputs. No admission or accepted-run restriction. |
| `stage2` | `∀ program accounts data slot, native2 program accounts data slot = AdapterRw.r1_pool_adapter.owned.stage2_owned O program accounts data slot`. Same unrestricted domain, with every `Slot`, including inner `Err` and every error payload, not just a successfully fetched clock. |
| `digestSource` | `∀ self parts, O.op43 self parts = S2W_DigestExtraction.digest hashv self parts`. Every `AdapterRw.SolanaDigest` (the emitted unit carrier) and `Parts = Slice (Slice U8)`. The output is outer `Result Digest`, `Digest = Array U8 32`; no success/totality assumption. The wrapper binds `hashv parts` then returns those bytes. |

`digest_eq_hashv` proves the wrapper's result equals `hashv parts`, even on `fail`/`div`. `sourceBoundary` derives the older extraction record; its three rows are not three more assumptions. `P1 sha256 H` separately asserts the realization equality; `RuntimeSyscall hashv sha256` separately constrains returning syscall values. Neither establishes an entry-function correspondence, nor should SHA realization be used to cover missing source refinement.

`S2W_D189Wrappers.first` reserves snapshots, calls `native1 program e.first data`, propagates rejection, and on success copies the checkpoint into account 2 under the separate std law, releases its guard, then cleans up allocation. `second` reserves snapshots, calls `native2 program (e.second secondSizes) data slot`, propagates rejection and cleans up, returning `e.heap`. These are distinct non-extracted wrapper interpretations. A contract only about real AccountInfo `stage1`/`stage2` acceptance cannot prove the unrestricted owned-function fields: the wrappers supply only selected snapshots and hide the returned checkpoint behind a copy.

## Rust contracts required by the fields

These are specification schemas for future Kani contracts, not compiled Rust annotations or certificates. Use actual frozen `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::{stage1_owned,stage2_owned}` (TX1/TX2 owned entries), not newly written lookalikes. The public AccountInfo `stage1`/`stage2` additionally require the existing snapshot/copy/allocator/wrapper gates. Digest is `SolanaDigest::digest` in `programs/r1-cost-probe/src/lib.rs:13`, whose body is `hashv(parts).to_bytes()`.

Define independent safe Rust `stage1_ref_O`, `stage2_ref_O`, and `digest_ref_hashv`, transliterating the SAME cohort SDK and all installed slots of `O`. They must not call the implementation being specified. Freeze their source, features, ABI/usize width, producer, operation dictionary and error encoding. Let `E` encode Rust inputs/results into the listed Lean carriers (preserving all bytes, flags, keys, lengths, discriminants, vector contents, and errors). Let `Run` denote an entire execution outcome, including normal return, panic/abort and divergence. `EncodeRun` maps a normal Rust `Ok/Err` to Lean `ok (.Ok/.Err ...)`, and abnormal outcomes to the explicitly matched outer constructors. This mapping is a semantic obligation, not an available Rust function that magically catches divergence.

Common requires: well-formed safe Rust values and valid borrowed memory, correct frozen representation/feature pins, and the certified external primitive interpretations (field leaves, copies, allocator, Vec/Box, hash syscall). No assumption of valid proof, correct account count, distinct keys, good instruction tag, successful borrow, successful clock, or acceptance. All such checks belong to the body/reference. Every Lean input must be representable, or a separate Lean proof must cover its complement; machine/Kani length bounds alone cannot justify a universal Lean field. If a partial caller domain is used for lower contracts, each caller must establish it; no such precondition may leak into the top fields.

For each item the exact target is:

```
requires: Common(p, a, d [, s], world)
ensures:  EncodeRun(Run(actual, p,a,d[,s], world))
        = EncodeRun(Run(reference_O, p,a,d[,s], world))
modifies: only fresh owned allocation/allocator-private state and the explicitly
          threaded external-effect state described below; no input memory
```

* **stage1:** actual `stage1_owned`, reference `stage1_ref_O`, result `Result<Vec<u8>, ProgramError>`. Normal-return ensures is `ret == stage1_ref_O(pre_program, pre_accounts, pre_data)` with exact error discriminant/payload or exact checkpoint length AND bytes. `modifies` excludes program, account metadata/data, instruction memory and every pre-existing account cell; permits private Vec/Box allocations and declared runtime effect state. The fresh returned Vec is owned, valid and disjoint from borrowed inputs. Reference evaluation uses an independent copy of the same initial external state, not the state after actual execution. Zero-copy aliases or pointer/capacity equality are not substitutes for contents equality.
* **stage2:** actual `stage2_owned`, reference `stage2_ref_O`, result `ProgramResult`. Normal-return ensures is `ret == stage2_ref_O(pre_program, pre_accounts, pre_data, pre_slot)` including exact errors. Requires permits both `Ok(u64)` and `Err(ProgramError)` clock arguments. Same input frame. `modifies` additionally names return-data/log effects reached by `emit_result` and observer effects; the reference must describe them, and every caller must frame them. An empty modifies set would be false if it suppressed those effects.
* **digestSource:** actual `SolanaDigest::digest`, reference `digest_ref_hashv(self, parts) { hashv(parts).to_bytes() }` under the same specified external `hashv` reply. Normal-return ensures is exact `[u8;32]` byte equality; `modifies` excludes `self` and every input slice, permits only declared syscall/query-log and private allocation effects. Requires admits empty parts, empty slices and duplicate parts; borrowed aliasing is allowed where Rust permits it. This certifies the source wrapper. It still takes a semantic association identifying installed `O.op43` with that wrapper; entry contracts alone cannot manufacture that association. Digest correctness relative to SHA-256 and ideal `H` remains in RuntimeSyscall/P1.

For all three, normal Kani `ensures` only runs on normal return. A proof that panics cannot occur plus exact normal-return equality is sufficient ONLY with matching Lean reference totality on the entire covered domain and a termination argument. Alternatively prove the displayed relational `Run` contract, preserving outer fail payloads/divergence. A finite unwinding, an assumed successful allocation, a fixture length cap, or agreeing only on successful results is insufficient by itself. This job does not assert these strong contracts are feasible or true for current pins. In particular, known error-to-panic differences obstruct literal equality unless the precise boundary proves them unreachable or uses a justified encoding; identifying both as generic rejection changes the relation and needs a different theorem.

Ordered attempted digest calls (arguments, replies, duplicates and every rejected prefix) must additionally match against a coupled reply world if used for adaptive experiment transport. State that relation as an additional effect postcondition; output equality does not imply it. Other declared observable effects require explicit reference relations as well. The three Lean fields above alone forget this history. Contract composition must retain the history for the separately audited trace consumers, not infer it from the fields.

Every future contract proof needs the ruling-(t) fidelity controls, per-shape and matched failing controls, verified callee contracts and coverage, no unproved stubs, and pinned unwind/overflow/panic/allocator policies. Rule 14 quarantines any property depending on function-pointer values/comparisons or `Option<fn>` observers. No Kani verdict, including a quarantined one, is credited here.

## The missing link and its classification

For each owned stage, Kani certifies a relation between two Rust bodies. Lean can check a separately extracted reference against the cohort SDK, but its arbitrary `native1`/`native2` parameter has no Rust denotation. An encoding/simulation must identify that parameter with the execution Kani actually compiled, identify the reference extraction with that SAME Rust reference, and justify transport of the certified relation over every Lean input/outcome. For digest the analogous transport must identify `O.op43` and `hashv` with the pinned wrapper and external syscall interpretation.

| Field | Link classification | Residual after a successful medium |
| --- | --- | --- |
| stage1 | **(b)** if the owner confirms the existing pinned Kani/P6 and Aeneas/D188 trust scopes cover their joint semantic interpretation; otherwise **(c)**, an unapproved semantic-correspondence gap. | Translation/encoding and concrete native-parameter association, domain/outcome completeness; no longer trust an unchecked algorithmic stage1=SDK claim once its certificates and reference proof really exist. |
| stage2 | Same **(b)/(c)**, independently instantiated for stage2 and slot/errors/effects. | Same boundary for stage2, including consistent external state and representations. |
| digestSource | Wrapper reduction is a checked Lean source-helper theorem; association with actual Rust, `O.op43` and `hashv` remains **(b)/(c)**. | Pinned wrapper/syscall interpretation and translation; RuntimeSyscall and P1 stay separate. |

None is **(a)** for actual Rust. One can DEFINE `native1 := stage1_owned O` and `native2 := stage2_owned O` and obtain the first two equalities by reflexivity, but that changes the instantiation to model functions without connecting it to shipped execution. Similarly, defining `op43` to equal the wrapper supplies a model instance, not a proof about the installed runtime. Source hashes and identical symbol names do not prove semantic correspondence.

Lean's proposed factoring has reference function values `ref1`, `ref2`, `refDigest`, checked model equalities `ref1 = cohort_stage1`, `ref2 = cohort_stage2`, `refDigest = digest hashv`, and the residual semantic interface:

```
native1 = ref1 ∧ native2 = ref2 ∧ ops.op43 = refDigest
```

These extensional equalities represent the RESULT projection of the trusted cross-tool transport after the Rust certificates are validated. They do not encode Kani PASS, tool semantics, traces, or artifact provenance. At the Lean level this factoring is equivalent to the old record once references are quantified and model equalities supplied: it is not a logically weaker premise or a discharge by repackaging. The reduction is in the scope of unchecked implementation trust, conditional on external evidence, not in the theorem's logical strength.

### Draft narrower trust row for OWNER decision; not adopted

> Native contract semantic transport (result projection). For only the frozen owned TX1 stage1, owned TX2 stage2 and SolanaDigest wrapper bodies, reference bodies, operation dictionaries, features, input/outcome encodings and tool versions enumerated by the accepted receipts, we trust that the Rust execution interpreted by Kani/CBMC and the reference execution interpreted by pinned Charon/Aeneas denote the same Rust language/primitive semantics under the certified common external world. We trust the explicitly recorded association of those Rust entries with the Lean function parameters native1/native2, of the digest wrapper with installed ops.op43, and of the external digest with hashv. Transport of the fully validated Rust contracts yields native1 = ref1, native2 = ref2 and ops.op43 = refDigest for every Lean input, with exact nested Result tags/payloads, provided representation coverage and abnormal-outcome/termination obligations have been discharged. This row supplies semantic interpretation only: the Rust contracts, fidelity/failing controls, coverage evidence, reference-to-SDK Lean equalities, and all primitive obligations must actually be present for the same pins. It licenses no acceptance-only substitution, unchecked stub, function-pointer-quarantined verdict, changed source, native attempted-call-trace conclusion, SBF/compiler equivalence, or cryptographic claim. Safe Vec/Box, allocator, copies, field leaves, runtime SHA and P1 retain their separately named boundaries.

The owner must decide whether this is an explicit narrowing/clarification of existing P6/D188 tool trust or requires a new row. Until then it is **(c) unresolved**, not silently approved under ruling (w), whose text says it adds no trust item. A trace extension would require its own exact statement/approval and evidence, not an implicit extension of this result row.

## Before/after and scope of progress

Before: the replayed theorem quantifies arbitrary `native1`, `native2`, `hashv` and takes all of `extraction : AeneasExtraction O native1 native2 hashv` as a premise, alongside runtime admission, P1, RuntimeSyscall, allocator/std and the remaining security premises. Its accepted executions are the wrapper executions, not assumptions that the owned entries already equal the model.

Potential after: SAME domains, SAME nested Result equality, SAME conclusion and security game, using (1) completed pinned Kani top contracts, (2) Lean proofs of extracted references = exact installed cohort SDK, and (3) the explicitly retained semantic transport row to construct `extraction`. No such Rust certificates/reference implementations/full reference proofs are supplied by NCQ. Replacing exact errors by generic rejection or limiting to snapshot/admitted/accepted inputs would instead change the theorem and requires a separate sufficient-refinement/experiment-transport proof.

Trust inventory rows 72–77 identify the current three-field extraction boundary and its derived older form; P6/P7 prose and D188-P2 qualify its scope. The historical-versus-release preparation/query/finish mismatch must be closed by SAME-pin association evidence, not tool trust. Neither (w), this proposal, nor a model-side theorem repairs it. Source-to-ELF correspondence remains separate P7/S10 work.

The medium can discharge algorithmic correspondence proof obligations within Rust and reference-to-model obligations within Lean. It cannot prove its own cross-tool semantic soundness inside the existing Lean language, attach arbitrary function parameters to Rust by definition, or establish the deployed security target from these three fields alone. Target not yet established.
