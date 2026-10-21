# Prover commitment continuation 7 — 2026-10-21

Branch `codex/cx-prover-commit7-20261021`, base `072b24afc`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit7-20261021/`.

## Exact cursor classification

`ProverCommitCursor.decoder_exhausted` identifies failure of the finite,
consuming sequential array decoder with `CommitReadsR1.Exhausted` whenever
`16 * L ≤ N`. The proof handles arbitrary word streams and every starting
cursor/retry state. It does not pad accepted limbs to sixteen words. It
proves the forward/reverse Kleisli iterations equal and transports the
finite suffix recursion to the actual `tryLimb`/`limbPos` definitions.

Focused env J **8243**: exit **0**, wall **2.09 s**, peak RSS
**4,034,836 KiB**, **zero swaps**; five verbatim audits use only
`propext`, `Classical.choice`, `Quot.sound`. Attempts 8240–8242 were
elaboration drafts, excluded. An unchanged-input preflight for 8243 was
refused before compilation; the proof was then corrected and 8243 used
normally. The refusal is not accepted verification evidence.

Further stage results, exact checklist changes and final audit follow below.

`ProverCommitSourceExhaustion.quotient_exhausted` transports the result to
exactly the existing two `wordsE` block carriers. Failure of the quotient
is **equivalent** to either stream's exhaustion. `caller_exhausted` shows
that the same caller equation required by the fibre transfer also suffices
for source exhaustion; there is no independent cursor premise once that
equation is proved. This does not prove the caller equation.

Accepted J **8245**: exit **0**, wall **2.76 s**, peak RSS
**4,170,036 KiB**, **zero swaps**, two standard-axiom audits. J8244 is an
excluded syntax draft. This closes the exact finite-decoder/cursor
classification sub-obligation, conditional source transfer stated explicitly.

## Typed caller interface and privacy endpoint

`ProverCommitCallerInstance.CallerLaw` is one named Prop with the two
canonical block budgets and an existential output-coordinate equivalence.
It requires the projected caller to equal the sequential decoder followed
by that equivalence on **every** pair of block-answer vectors. This permits
the source's actual cell order rather than requiring `Fintype.equivFin` to
be its enumeration. `fibres`, `exhaustion`, and `budgets` derive all previous
fibre, RExh, stream, counter, cell-count and block inequalities from it.
The caller law itself is not proved or installed as an axiom.

`PrivacyR1FinalProtocolCaller.privacy_R1_protocol_caller` is built directly
on `PrivacyR1FinalProtocolQuotient`. At the M31 image subfield, it replaces
those separate premises and free cF/L₁/L₂ parameters with this law, the
proved `quotientFibreSize`, and the canonical `L₁/L₂`. Its conclusion is the
same experiment, simulator and error expression specialized to those two
counts, including the strict 2^-100 bound. Wire execution joins and builder
premises remain explicit. It does not assert universal source read coverage.

Accepted final J **8250/8253**: exit **0**, wall **2.55/3.25 s**, peak RSS
**4,045,904/4,074,780 KiB**, **zero swaps**; seven standard-axiom audits.
J8249 is the accepted, narrower exact-order prototype; the final law
explicitly supports the required coordinate bijection. Other drafts
8246–8248 and 8251–8252 are excluded. All literal attempted sources are
retained. Only this branch's new modules/objects are installed or replaced;
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are untouched.

## P6 caller route: verified scalar callees

The shipped `SeedExpander::next_word` and `Profile21SourceExpander::next_word`
now have proof-only contracts. Each checks the whole owned-state reference,
including cached/refill cases, wrapping counter, block, word cursor and
unchanged seed. Both `proof_for_contract` harnesses pass. The
`mask_limb_caller` harness then directly executes the **actual shipped
sixteen-try m31 method**, using `stub_verified(next_word)`, and compares its
result and every state field to the owned early-return `limb_caller`.
It passes, including the exhaustion return. This advances beyond the old
copied single-try/Lean-composition boundary. It does not certify the outer
material-building loops.

The shared read-only memoised oracle assigns unconstrained digests to nine
distinct consecutive counter messages, enough for four scalar calls from
any valid initial slot. Both sides use the same table without resetting it.
The finite-oracle harness checks every slot, arbitrary seed/base counter,
wrapping, and repeated queries. Digest collisions remain permitted. Every
hash call asserts its complete domain/seed/counter frame and range. This is
a classical-ROM function certificate, not a SHA-256 algorithm proof.

Accepted normal-exit receipts: mask/source next-word contracts
**19.935/19.702 s**, finite oracle **139.916 s**, mask m31 caller
**382.619 s**. Peak RSS respectively **2,072,924 / 2,065,152 / 6,159,052 /
2,175,164 KiB**; zero swaps. All checks use 6G/8G/zero-swap/64-task scopes,
four compiler jobs, and the four-thread linker flag. Time is in proof
compilation and CBMC, not native arithmetic. Kani has no `#print axioms`;
its external soundness boundary is kept distinct from the Lean theorems.

Two excluded 600-second trials are retained verbatim: a general-table
caller comparison and the first next-word contract formulation. The
replacement removes repeated generic input flattening and disables only
optional assertion-reachability analysis; assertion validity, safety and
explicit unwinding checks remain enabled. It also uses CBMC's embedded
CaDiCaL. No cap increase or unchanged aggregate extraction occurs. Timeout
GNU-time parent RSS is incomplete; the recorded cgroup peak is authoritative.
The source/D scalar and four-coordinate comparisons continue separately.

The source/D whole-scalar comparison subsequently passes too: **342.491 s**,
**2,222,956 KiB** peak RSS, zero swaps, exit 0. Its input source snapshot is
identical to the accepted scalar-stage snapshot. Both shipped scalar
methods are therefore compared directly, not inferred from a copied try
body. The first four-coordinate trial was deliberately stopped after
**68.969 s** (exit 143, excluded) to replace nested scalar unfolding with
checked scalar summaries. Its receipt and the own-process orchestration
record are retained; no peer job was stopped.

## Owned reference extraction and remaining caller obstruction

The adopted reference is extracted alone, not the obstructed aggregate
source caller. Charon v3 and Aeneas v3 both exit 0 (24.597 / 0.481 s,
670,856 / 82,192 KiB RSS, zero swaps). The LLBC reports `has_errors=false`.
The generated namespace `AspisR1ProverCaller7` contains the exact next-word,
early-return scalar and left-to-right four-coordinate bodies. P is concrete;
there is no external CM31 constructor or other opaque generated callee.
The only Types port is the existing Aeneas discriminant attribute migration.
The hash function remains a parameter; this does not extract SHA-256.

J8254/8256 compile Types/Funs separately. J8260 proves explicit state-carrier
roundtrips and equality of the new and previous next-word extraction,
including Aeneas fail/div. J8265 proves the actual signed-range early-return
loop equals a structurally recursive finite evaluator and specializes it to
sixteen attempts. No recurrence or concrete oracle digest is normalized.
J8255 separately proves coverage of the nine valid initial word slots and
seven counter offsets; these are index facts, not source read completeness.
Every new theorem has an accepted standard-axiom audit. Draft failures
8257–8259, 8261, 8263–8264 are excluded; 8262 is the accepted iterator-only
predecessor. Exact source, dependency, time and audit records accompany all
attempts in the evidence directory.

The reference next-word and read-only hash callback contracts also pass
(34.792 / 17.242 s, 1,133,848 / 763,376 KiB, zero swaps). The attempted scalar
summary and nine-case variants each reach the 600-second review limit
without a verdict. Their unverified contracts and checkers were removed
from adopted Rust. The actual four-coordinate comparison with only the
verified hash callback also times out at 600.030 s; the actual 1024-row
balancing-helper comparison times out at 600.108 s. Neither is accepted.
The earlier direct four-coordinate trial stopped at 68.969 s is likewise
excluded. No source scalar summary is used as `stub_verified` without a
passing proof. The later source four-coordinate and four-coordinate
balancing targets were not run after these obstructions.

These experiments demonstrate the remaining compositional obstruction:
the passing scalar certificates have not yet been promoted to reusable
scalar contracts that cover all successive stream states. The extraction
and finite evaluator do not themselves prove the owned-reference-to-wordsE
carrier/cursor equation, the outer material loop identity, or its coordinate
bijection. `CallerLaw` therefore remains a named hypothesis, not a theorem
about the shipped caller.

## Selected leaf frames and read coverage boundary

The memoised concatenated-byte oracle now accommodates the selected binary
C1 leaf frame: 480 value bytes plus tag prefix and 32-byte salt (514 bytes
total). The selected C2 frame uses 128 value bytes (162 total). Both actual
private-leaf helper comparisons pass, including the actual HOST_HASH route:
C1 148.458 s / 1,790,756 KiB; C2 26.450 s / 656,568 KiB. Generic regrouping
and callback tests pass at 30.926 s / 810,016 KiB and 8.605 s / 504,636 KiB.
All exit 0 with zero swaps. These add the selected widths to the earlier
416/192-byte fixtures. They prove helper framing, not that every outer
producer has the expected packed value, typed address, and complete read
coverage. In particular a salt derivation can repeat a binding read;
physical callback count is not a bijection with distinct typed coordinates.
No universal read-coverage theorem is claimed.

## Before (verbatim from continuation 6 after-table)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input; the actual source/caller/order/field-image equation remains open. |
| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Quotient packing adds no failures; the source caller/cursor law and exact wordsE-to-Exhausted classification remain open. |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |
```

## After (verbatim; nine complete shipped-source rows remain open)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input. The new endpoint derives this premise from one typed CallerLaw, including an output-coordinate equivalence; proving CallerLaw for the actual source remains open. |
| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Exact consuming wordsE-to-Exhausted classification is proved, and the endpoint derives this premise from CallerLaw. The shipped source-to-decoder caller/cursor equation remains open. |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved and derived in the endpoint from CallerLaw. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |
```

The new `PrivacyR1FinalProtocolCaller.privacy_R1_protocol_caller` is built on
`PrivacyR1FinalProtocolQuotient`. Its printed conclusion has identical text
under the documented specialization to the M31 image subfield and canonical
L₁/L₂. The signature audit records twelve removed parameters/premises and
the single remaining caller law. This is a conditional reduction of the
checklist, not a proof of the remaining law or a closure of a complete
shipped-source row. The exact cursor-classification sub-obligation is closed.

## Final audit, executable artifacts and stopping point

Final coherent new-cone audit `R1Z.ProverCommit7Audit`, J8266: exit 0,
wall 1.71 s, peak RSS 4,043,344 KiB, zero swaps. Source revision
`9e6c55ba8` contains all adopted theorem/Rust sources; the additive audit
module and its exact SHA/dependencies are recorded with its receipt.
All 23 new audit lines contain only propext, Classical.choice, Quot.sound
or a subset. Existing compiled dependencies are reused; there is one final
new-cone audit, no unchanged package replay, and no aggregate extraction.
Assigned attempts consumed through 8266; next available is 8267.

After the last Rust source edit, all three frozen SBF artifacts were rebuilt
in dedicated 6G/8G/zero-swap/64-task scopes with four jobs. Compilation and
linking are optimized SBF, not debug arithmetic. `build.py` records the exact
frozen features/toolchain and linker flags; the SBF linker uses its target
`--threads=4` spelling. All three `cmp` calls return 0 against retained
accepted artifacts, with the accepted SHA-256 values:

| Artifact | SHA-256 | Wall s | RSS KiB |
| --- | --- | ---: | ---: |
| default | dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34 | 23.895 | 648608 |
| devnet | fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 | 2.219 | 203364 |
| pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 24.020 | 642416 |

All exit 0, zero swaps. Sizes, exact commands, source hashes and scope
receipts are in `frozen-elf-final-check.json` and the receipt index. Only
proof-configuration Rust code/attributes changed; shipped bodies did not.
No wallet/key cleanup, transaction, deployment, push, peer-file edit, or
merge was performed. Build keys and caches are retained on the host.

The demonstrated obstruction is repeated bounded-checking timeout after
callee isolation, not a theorem counterexample. The final live source has
no unverified scalar contract. Remaining work is a scalable, verified
scalar summary over successive oracle states, four-coordinate/outer-loop
identity and source-to-wordsE transport, then universal typed read coverage
for trees, bindings, seeds and salts. Repeating the same direct qM31 or
1024-row proof unchanged is not justified by these receipts.

`harness/validate.py` validates all 27 attempted Lean source identities
(12 accepted targets/prototypes), all 23 final axioms lines, all three ELF
comparisons and the complete Rust receipt-to-source mapping, without
replaying any build. Raw stdout and the literal generated-port diff retain
upstream trailing spaces; whitespace warnings in those evidence files are
intentional. The adopted code has no such whitespace errors.
