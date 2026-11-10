# Trust inventory

Every machine-checked proof rests on something it does not prove. For the
current version the line is drawn at the frozen Aspis source, so that Aspis's
own code is proved and everything outside it is trusted through a named
assumption with a precise statement. This page sets out those assumptions, says
where each one enters the proof, and gives the condition under which it could
be removed. Most are settled, a few about the Solana runtime are still
provisional and are marked as such, and some have no removal condition recorded
yet.

The first kind of assumption is cryptographic. All the probabilities in the
soundness theorem are taken over SHA-256 modelled as a random oracle, a
uniformly random function, as the program invokes it through the runtime's hash
syscall. A few further assumptions connect the program's actual hash calls to
that oracle, saying that a hash call that returns gives the SHA-256 of its
inputs and that the value returned is the oracle's value. The random-oracle
model itself has no removal condition, since an argument in the standard model
would be a different theorem.

The second kind concerns the Solana runtime. The runtime is trusted at the specific points where the
verifier relies on it: that each entry point starts with a valid heap and fresh
borrow guards, that account data written by a successful transaction is what
the next transaction on the same lineage loads, and that a handful of syscalls,
for return data, memory comparison and the clock, behave as documented. Each
assumption is stated narrowly; the clock assumption, for example, says only
that a successful clock read reports the current bank slot, and nothing about
when the read succeeds.

The third kind concerns code and tools outside Aspis: the documented borrowing
behaviour of the Solana account library and of Rust's `RefCell`, the standard
library's slice copy, the Charon and Aeneas tools that
translate Rust into Lean, the Kani model checker used where translation was not
possible, and the compiler and pinned libraries. The translation is trusted to
preserve each function's accepted result and the order of its hash calls, with
narrowings for the patterns where the tools are known to go wrong. Tool trust
does not by itself connect the source to the deployed binary; that connection,
and the difference between the checked arithmetic of the translations and the
wrapping arithmetic of the deployed program, are separate obligations tracked
in [`OPEN-GATES.md`](OPEN-GATES.md). The logical base is Lean's three standard
axioms.

The last kind is the reviewed transcription. For some functions the pinned
tools could not produce a translation, so a reviewed stand-in takes the place
of the frozen body: either a hand transcription of a reference function, tied
to the frozen code by Kani, or a copy of the frozen body in which named calls
are replaced by logging windows and which is checked mechanically to equal the
frozen body apart from those substitutions. What is trusted is the
correspondence the stand-in asserts. These are recorded as a reclassification
of the existing translation and Kani trust, never as a removal of anything.

Since 10 November 2026 no trust assumption is accepted unless it is a standard
Solana runtime or Rust library operation. A reviewed transcription of
Aspis code is therefore not a permanent assumption: each is to be discharged by
a translation proved equal to it, the statements that use it are conditional
until then, and functions that no tool can yet translate stand as open
obligations. Under the same rule the transcription of the public-preparation
accessor was withdrawn as a trust item (its proofs stay as evidence, and the
newer tool now translates the function, which is proved equal to its fresh
translation with no assumption named), the transcription of the compiler-derived clone
and equality operations stays because those are compiler derives, and the
deployment-id constant entered the SDK assumption with a receipt comparing it
byte for byte with the deployed ELF. The rule covers the transcriptions accepted
earlier, on 27 October 2026, as well, so those too are open obligations and the
statements that use them are conditional until a translation is proved equal.

Some things in the theorems look like conditions but are not trust. The query
budget is a parameter of the statement, the Q of the bound; the two-transaction
game and the requirement that both transactions succeeded describe the
experiment; and the allocation streams are universally quantified data. The
historical checkpoint interfaces from earlier versions are not relied on, since
the history the theorems need is derived from the game, the persistence
assumption and source proofs.

This inventory was taken from the `research` branch before it was reconciled
one to one with the final proof closure on 10 November 2026. The reconciled
table, which gives a removal condition for every assumption the theorems reach
and marks those they do not reach, is section 4 of
[`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md), and what remains to be confirmed
is in [`OPEN-GATES.md`](OPEN-GATES.md). The tables below give the detail, under
the names the ledger, the status document and the Lean sources use.

## Reference: the oracle model

| Assumption | What it says | Where it is used | Removal condition |
| --- | --- | --- | --- |
| Random-oracle model for SHA-256 | SHA-256, as invoked through the runtime's hash syscall, is a uniformly random function H; every probability is over H | Every probability statement in the theorems | None; a standard-model argument would be a different theorem |
| P1, ideal-oracle realisation | The fixed native digest equals the sampled oracle at the world supplied; an interpretation of the model, and no proof that SHA-256 is random | Instantiated directly with the digest set to H; justifies reading the physical hash replies of a run as values of H | None; inherent to the random-oracle reading |
| `RuntimeSyscall` | A hash call that returns successfully returns the SHA-256 of the concatenated input slices; nothing about totality or termination | Instantiated by a theorem; justifies the physical reading of every returned hash | A proof that the pinned runtime's hash syscall returns exactly that; not recorded in the inventory at the time |
| `RuntimeSha256Value` | The value returned by the SDK's hash wrapper realises H; exact request slices and an unchanged reply are separate bridge obligations | Retained value uses in two verified statements | None recorded |

## Reference: the Solana runtime

| Assumption | What it says | Where it is used | Removal condition |
| --- | --- | --- | --- |
| `RuntimeEntrypointAdmission` | At each of the two verifier entries the heap is valid, borrow guards are fresh, counters and external borrows are zero, accounts are live, and keys and cells alias consistently | Part of the description of the run | None recorded |
| `RuntimePersistence` | When the next transaction on the same bank lineage loads an ordinary account, its data bytes are the previous transaction's final bytes if that transaction succeeded, and its starting bytes otherwise; data bytes only, zero lamports meaning absent | Part of the description of the run; supports the checkpoint between the two transactions | None recorded |
| `Allocator` | An allocate and clean-up interface carrying data only, with no promise of success | Instantiated so that a failed allocation aborts, so a run that returned had no failed allocation; that physical reading falls under the allocator, compiler and ELF realisation below | Not applicable as a free assumption |
| `RuntimeReturnData` | Setting return data of length 1 to 1,024 and immediately reading it back in the same instruction, with no cross-program call between, returns exactly that data and program | One verified use, where the verifier emits its result; the pool's side of the readback is outside the theorem | None recorded; accepted by me on 4 November 2026 |
| `RuntimeReturnDataClear` | Setting empty return data leaves nothing observable until a later set, within one instruction | The second stage clears return data before emitting its result | A proof of the pinned runtime's return-data register |
| `RuntimeMemcmp` | The runtime's memory comparison of the same two valid 688-byte ranges returns normally, gives zero exactly when the bytes are equal, and has no other effect; nothing about ordering, sign or timing | The proof-buffer scan | A trust-reduction study of the pinned validator, recorded but not commissioned; accepted by me on 4 November 2026 |
| `RuntimeClockSlotBinding` | When reading the clock succeeds, the slot it reports is the bank slot of the executing transaction; nothing about success, monotonicity or epochs. An error reply is covered as a runtime reply, and an allocation failure while building it is an abort | Both clock reads in the source, and every forwarded current slot | A proof of the pinned clock sysvar |
| `RuntimeCpiAccountView` | After a cross-program call by the pool that returns, accounts not passed to the callee are unchanged and accounts passed show the callee's final values; nothing about token or system programs, success of the call, rent or rollback | The pool's cross-program calls only; relevant only if the pool's execution enters the claim | A proof of the deployed runtime's account update after a cross-program call |
| `RuntimeEntrypointAdmission-Pool` | The same seven facts as entry-point admission, at the pool's entry point | No verified verifier statement | None recorded |
| `RuntimeCpiReadonlyEntry7` | Pending | Not relied on | None |
| `FixturePdaRuntime` | For seven fixed test invocations the runtime's program-address derivation agrees with the model; the off-curve facts and digest equations for those seven are proved, so only the syscall's agreement with its documented algorithm is assumed | The non-vacuity witness only; never used by the soundness theorem | None |

The return-data, clock, account-view and pool-admission assumptions, and the
fixture derivation assumption, are provisional and have still to be confirmed
one by one.

## Reference: the SDK, the standard library and the tools

| Assumption | What it says | Where it is used | Removal condition |
| --- | --- | --- | --- |
| `S2TrustedSdkBorrow` | The documented borrowing behaviour of `solana-account-info` 2.3.0 and of Rust's `RefCell`, `Ref` and `RefMut` guards, as fifteen fields covering acquisition, movement, dereference and drop of guards, error handling, framing and liveness. It supplies no caller result or output bytes, and does not cover reference cloning or splitting, reallocation, lamport borrows, cross-program calls, re-entrancy or concurrency | A binder of both theorems | None recorded; the pinned Aeneas cannot yet translate guard drop, so there is no tool route to a proof |
| `TrustedStd`, slice copy | The pinned `copy_from_slice` on valid borrowed references: equal lengths copy into the destination only, unequal lengths panic. The abstract law is stated over all states, so every actual use must have its validity justified (qualification W1) | A binder of both theorems | None recorded; W1 must be met at each use |
| `TrustedStd`, Option and Result | The pure meaning of `Option::ok_or` and a 32-byte `Result` unwrap, accepted on 22 October 2026 as separate items | Not reached by the theorems | None recorded |
| `AeneasExtraction` (D188), trace fidelity | The pinned Charon and Aeneas translation of each associated frozen body preserves the accepted result and the chronological sequence of attempted hash calls, rejected prefixes rejecting on both sides. Bodies that fail the scan for dropped writes or the native differential test get no credit and are bridged natively. The translation is taken as faithful except for explicit returns or `?` in code after a loop that has been merged into the loop's exit, so each body relied on must be free of that pattern or have the affected exits certified natively | Every verified statement whose proof uses a translated body | None for the tool. For the release, every reached translation must be reproduced from an archived input or proved equal to a fresh one |
| P6, Kani association | The pinned Kani model checker as evidence for checked associations between a frozen body and its reference. Credit only without copy built-ins, or with the recorded element-wise copy stubs and a matched failing negative control; timeouts earn nothing | The native halves of the hybrid statements | None for the tool |
| `NativeContractSemanticTransport` | For the enumerated frozen stage bodies, the hash wrapper, their references and the recorded tool versions, Kani's and Aeneas's readings of the Rust denote the same semantics, and the recorded association of the Rust entry points and digest wrapper with the corresponding Lean parameters holds. A clarification I approved on 28 October 2026 of existing P6 and D188 trust, with no new kind | 380 verified statements | None recorded |
| P7, compiler and pinned libraries | The compiler, LLVM, platform tools and ABI, and the release-pinned Lean, Mathlib and Aeneas libraries, for the exact source, features and toolchain recorded | The whole closure | None for the tool; the source-to-ELF association is a separate obligation |
| `AllocatorABICompilerSourceToELF` | The binding of the proof to the concrete final artefact, including the physical reading of the allocator | The root realisation | Discharged only by the final audit |
| `CheckedVsWrapping` (R22) | The translations were made with overflow checks on while the deployed program wraps, so the theorems are about the checked semantics; carrying them to the binary needs, on every reached path, that no checked operation fails or that wrapping acceptance implies checked acceptance with the same result | Every verified statement whose proof uses a translated body | Discharged when that audit closes on the final closure, or if it is recorded as a retained assumption; current state in [`OPEN-GATES.md`](OPEN-GATES.md) |
| Standard logical axioms | `propext`, `Classical.choice` and `Quot.sound` only, for each top theorem and audited root | The kernel | None. The imported libraries also hold 105 nonstandard axiom declarations; none is reachable from the top theorems or is a premise, but a strict check that every import uses only standard axioms still fails |

## Reference: reviewed transcriptions

| Function | What is trusted | Removal condition |
| --- | --- | --- |
| `stage1` in the verifier's pool adapter | That replacing the snapshot, the call into the first stage, the mutable borrow and the slice copy by logging windows preserves the frozen body's behaviour; the pinned Aeneas cannot translate the frozen body because of `RefCell` guard drop | A native certificate on the frozen function, proved equal to the same fold |
| `stage2` in the verifier's pool adapter | The same, with the return-data clear, the seven snapshots, the clock read and the call into the second stage replaced | The same |
| `decode_lane_from_pool_release` | That the reviewed safe reference is a faithful transcription of the decoder, tied to the frozen code through a Kani contract checked against it for every lane length | A translation of the frozen decoder proved equal to the same fold |
| `prepared_claim` | A hand transcription of the reference, with the frozen function proved equal to it by Kani | A translation from the pinned extractor, or an approved successor, proved equal to the transcription |
| `queries_from_pairs` | A reviewed transcription of the reference, tied to the frozen function by membership harnesses and a native loop association | The same |
| A polynomial fold | A reverse-fold transcription | Not recorded |
| The batch tree | A transcription of the reference with native segment contracts at every exit | Not recorded |
| Five pool functions (global root, return-data read, marker seed, next lane, leaf-witness validation) | Source-fission or hand-composition transcriptions | A native certificate on the frozen function, or a translation proved equal |
| The pool's account-count check | Only the replacement of the slice length by a parameter | A native harness on the unmodified body over all slice lengths, or a translation proved equal |
| 36 further verifier-side items, each used by the statement it names | Reviewed transcriptions of references | At the time this inventory was taken, none had its own; the class default is a translation from the pinned extractor, or an approved successor, proved equal to the transcription. The reconciled table now gives one for each |

The pool transcriptions are used by pool statements only and by no verified
verifier statement. They are listed because the theorems' description of a run
names the pool's actions, and because they would enter if the pool's execution
were brought inside the security game.

## Reference: the approved appendix of 27 October 2026

The inventory rests on a trust appendix that was approved on 27 October 2026
and incorporated into the security contract. It was written as a proposal
and is retained verbatim at the source linked below; where its text says "not
adopted" or "candidate", the contract amendment controls, and for the
translation tool the trace-fidelity reading was chosen. Its main records and
qualifications are these.

| Topic | What the appendix records |
| --- | --- |
| Field inventory | All 44 fields of the trust structures, one to one: 15 for the SDK, 9 for entry-point admission, 7 for historical checkpoint interfaces, 6 for translation, 3 for the standard library, 2 for the allocator, 1 for the ideal oracle and 1 for the hash syscall. Each is marked as named in the contract, accepted by a cited earlier decision though not literally named, or unrecorded, in which case no acceptance is inferred and the item stays a finding |
| Wider surfaces | 8,565 pinned library implementation surfaces covered by the compiler and translation base; 551 repository implementation surfaces, unreachable from the theorems and not extra trust; the 105 nonstandard imported axioms, each kept individually so that none disappears into tool trust |
| Proof obligations, not trust | Unsafe source code using uninitialised memory or raw writes, child joins and source-event traces |
| Scope limits | The SDK assumption supplies no caller success, output bytes or complete execution refinement; the standard-library assumption keeps W1; the ideal-oracle realisation adds no identity between native hashing and every sampled oracle and no new cryptographic assumption; the Kani route accepts the tool boundary but neither an unchecked association nor an enlarged domain; the compiler base applies only to the exact pins and does not prove a source-to-ELF association; the three standard axioms are permitted without accepting the 105 nonstandard ones |
| Rejected paths | On one rejection the Rust returns a parse error where the translation fails with a panic after ten of twelve leaf hashes, so identical error kinds on every rejection are not claimed; accepted results and effects must agree, and rejected prefixes must both reject and count the reads made before rejection |
| First-transaction preparation (D188-P2) | The selected translated models represent a retired version of the first transaction at five preparation interfaces whose association with the frozen source is not established: the dot-product type (historical sums with a count against the release sums), the prepared claim (a scalar against a 29-element array of powers), the query geometry (the release caches a line coordinate), the first transaction itself (a retired eight-way dispatch against the release's compact, batched path) and a retired finishing step with no release counterpart. The theorems remain valid about their selected model, but attributing them to the deployed code across this boundary is qualified until association proofs close against the same release source. The pinned translator fails on six release functions on this path, and the chosen route extracts the rest with those six as opaque leaves handled through an owned reference, Kani and a Lean correspondence. The status document lists this attribution among the things not claimed unless the final audit shows the five interfaces covered by native bridges |
| Dropped write (D188-P3) | The pinned translation of one sampler function drops a write the frozen Rust performs, so that body gets no credit; credit for four related bodies was suspended pending per-function checks, the recommended repair being to narrow the translation assumption and bridge those bodies natively |
| Later additions | The clarification of 28 October 2026 on Kani and Aeneas semantics, the adoption of the fixture address-derivation assumption for the non-vacuity witness only, and the runtime and transcription assumptions added from 4 to 10 November 2026, all included in the tables above |

## Where this comes from

This page is written from the `research` branch at commit `07123926e88`. Its
reference tables follow section 4 of the status document as it stood there,
and the last table summarises the approved appendix,
[`TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md`](https://github.com/DJBarker87/aspisZK/blob/07123926e88273271344977a3fdc26d1780cde14/design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md),
whose full text, field table and evidence links are at that link. The
reconciled inventory is section 4 of [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md).
