# Candidate 6 — complete relative equivalence proof

Public-decoding reuse, commit `e5a93db5c9a4883245dc575eaa94742f9adeb629`, is
proved equivalent to its parent with all other changes fixed, **under the
reference's existing source/runtime assumptions**. The retained production tip
is `39c2971dd16c95858a4cfd2c9ae35da052eacfa9`; no production Rust changed here.
This closes one retained optimization. The other nine and their combined
soundness/privacy transfer remain open.

## Exact theorem and scope

`CuSavingsPublicDecodeCallsite.source_eq` is the final consuming call-site
theorem: it combines the exact boxed decoder, actual total selector, argument
construction and the common adapter context. The earlier
`CuSavingsPublicDecodeClosed.actual_adapter_eq` instantiates the checked actual
reference decoder and selector and equates the complete old/new adapter
computations for every input, proof, query split, observer, rejection function
and common surrounding context. The context retains validation and checkpoint
processing and can carry returned state/effects in its output. There is no
new decoder-success, selector-success, downstream-success or optimization-
equivalence premise.

`adapter_eq` is the general contextual theorem; `observations_eq` preserves any
observation of its complete Result, including successful bytes/state/effects,
errors and divergence. `transfer_contract` transports any existing reference
contract using this equality; its only contract premise is the original
reference contract itself. This permits the original acceptance/formatting and
terminal-rejection premises to be retained when this one replacement is made.
It does not prove the other optimization contracts or re-prove a security game.

The implementation observations are those of the reference model: immutable
byte inputs, existing Aeneas primitives, faithful source interpretation and the
same enclosing SDK/runtime context, with sufficient resources. The proof does
not introduce a new compiler, SDK, Box allocation, timing or exhausted-resource
assumption. It also does not claim a new proof of compiler or SDK correctness.
Those pre-existing trust/runtime boundaries remain visible.

## Gaps discharged in this checkpoint

1. **Actual boxed decoder.** The exact unchanged Rust body is strictly emitted
   using the original pinned reference producer. The complete emitted body is
   compared to `boxedSource` after a recorded, explicit parametric binding of
   decoder, statement/error carriers and the constant error closure.
   `boxed_eq` identifies this complete computation with the existing decoder
   projection, preserving every error/divergence case. Box::new is erased by
   the unchanged reference producer; `projection_eq` uses the original
   Aeneas Box.deref definition and has no axioms.
2. **Earlier argument evaluation.** The new call evaluates semantic_public at
   the call site. `CuSavingsPublicDecodeOrder.actual_boxed_eq` binds the actual
   earlier decode, and `select_after_box` consumes the original
   PreparationBinding.actual_selector_eq to prove that selection is pure and
   total on its returned value. `argument_order_eq` commutes selection past
   arbitrary argument construction, including failure/divergence. The final
   theorem obtains the necessary decode result itself; it does not demand a
   decoder-success premise from its caller.
3. **Complete source delta.** Existing whole-source checks verify stage1 differs
   at exactly one call; wrapper inlining reproduces old first; the new decoded
   suffix is the old tx1/error-map suffix; and the same immutable public-data
   binding supplies the earlier decoder and verifier. Public/proof bytes and
   checkpoint processing remain in that common source context.
4. **Consuming call-site theorem.** CuSavingsPublicDecodeCallsite.source_eq
   combines these obligations in one equality, using arbitrary partial argument
   construction and the actual decoder/selector. Its observations_eq preserves
   observations of the complete computation. No decoder-success premise is
   exposed.
5. **Actual existing results.** Existing entry_success and
   entry_helper_parsePublic remain consumed. These supply the actual raw
   decoder, selected semantic public, serializer/public parsing and initial
   transcript facts. The historical helper theorem's Some mark specialization
   remains exactly its original scope. The contextual equivalence theorem
   itself holds for every observer, including None; candidate 2 is separate.

## Parametric wrapper interpretation

The wrapper extraction reuses the retained first-diagnostic kit's complete
statement declarations. Its decoder/error stub **implementations are not proof
interpretations**, and its diagnostic nominal error types are not claimed to be
real SDK types. The wrapper performs no inspection of those carriers: it calls
the decoder, maps any decoder error to one fixed error, applies Try and boxes
the returned statement. The consuming Lean definition universally quantifies
those carriers and binds the decoder to the existing actual reference model.
The source audit checks every emitted control-flow operation after these
explicit substitutions, including the constant error closure. No generated
axiom template or diagnostic function implementation is imported into the proof.
This follows the reference's existing parametric caller interpretation.

## Checks and evidence

`check-public-decode-closed.py` is the candidate-specific requirement audit.
`CANDIDATE6-COMPLETION.json` records its exact source/receipt hashes, bindings,
inherited boundaries and requirement-level results. It revalidates the prior
four caller/helper receipts and their original cache-owner objects without
recompiling unchanged targets. The complete old/new source snapshots remain in
`tools/cu-equivalence-20261019/public-decode-source/`.

| Focused target | Receipt | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| CuSavingsPublicDecodeClosed | cu-public-decode-closed-a | 0 | 4.008 | 3,782,536 | 0 |
| CuSavingsPublicDecodeOrder | cu-public-decode-order-b | 0 | 4.209 | 3,851,764 | 0 |
| CuSavingsPublicDecodeCallsite | cu-public-decode-callsite-a | 0 | 3.809 | 3,851,836 | 0 |

All declared/consumed results print standard Lean axioms only. The Box projection
has no axioms. Exact commands, source revisions, features, source copies,
checked imports/cache owners, stdout, exit/wall/RSS and process/cgroup swap are
retained per receipt. Jobs use the latest user-authorized uncapped NUC policy.
`cu-public-decode-order-a` is a failed local proof attempt, superseded by the
projection-normalization change in order-b; it is not successful evidence.

Strict source emission: cu-public-box-charon-a, exit 0, 0.401 seconds,
192,780 KiB RSS; cu-public-box-aeneas-a, exit 0, 0.401 seconds, 61,248 KiB RSS.
Both observed zero swap. The original producer SHA-256 is
`4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`,
with -checks and -abort-on-error. No toolchain expansion or compiler change was
needed. Codec/CU/runtime suites were not repeated for proof-only changes.

## Completion requirements

| Requirement | Authoritative evidence |
|---|---|
| Exact first/first_decoded/boxed decoder/stage1 delta and immutable bytes | Existing check-public-decode-source.py plus new complete boxed-body substitution audit |
| Box projection and call-argument evaluation order | boxed_eq, axiom-free projection_eq, actual_boxed_eq, select_after_box, argument_order_eq |
| All result paths and enclosing observations preserved | Final CuSavingsPublicDecodeCallsite.source_eq/observations_eq, actual_adapter_eq, adapter_eq, transfer_contract |
| Existing actual decoder/selector/helper/serializer consumed | entry_success, entry_helper_parsePublic, actual_selector_eq; pinned original owner cache |
| Focused checks, axioms, source/tool/cache pins and metrics | CANDIDATE6-COMPLETION.json and exact focused/source-emission receipts |
| Commit/push on side branch, root/production unchanged | Delivery verified against origin/codex/r1-cu-savings-20261019 when closing the goal; source checks pin production Rust and Git confirms the delivered commit |

Delivery is checked against Git after committing this certificate; the file
cannot contain its own commit hash. Only this candidate's proof and evidence
are included. Unrelated untracked gamma experiments and NUC cleanup material
remain untouched.
