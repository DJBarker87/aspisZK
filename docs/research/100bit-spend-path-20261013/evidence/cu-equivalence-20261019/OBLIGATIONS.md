# CU optimization equivalence — completion requirements

Goal: full equivalence proofs connecting the retained optimized verifier to the
reference used by the existing soundness/privacy results, with no new unproved
equivalence premise at the final transfer boundary. This is **in progress**.

Reference: origin/research f458169f705f25b04e1e29546c621e4665e0f64c.
Optimized production source: 39c2971dd16c95858a4cfd2c9ae35da052eacfa9,
unchanged through worker head 925dc4b95ad6986fd76471fca857d4e2100f1cbf.
Existing candidate declaration inventories remain authoritative inputs.

The observation relation must preserve acceptance/rejection, cryptographic
query input/answer order, public/proof/checkpoint bytes and settlement effects.
Internal diagnostic log erasure must be explicit. Equivalence compares logical
executions with sufficient resources; it does not equate failure under an
insufficient compute/heap cap. Resource bounds and source caller admission
remain obligations, not hidden hypotheses asserting the conclusion.

| Retained change | Required proof and source bridge | Status |
|---|---|---|
| 1 gamma table reuse | power table correctness, unchanged caller dataflow, preparation/tx1 extraction | open |
| 2 opt-in observer | observer state noninterference, diagnostic-log projection, caller feature binding | open |
| 3 S2 inactive groups | literal table correspondence, finite regrouping, source execution | open |
| 4 delayed base dots | modular equality, all u64 bounds, decoder/failure-order and loop execution | symbolic arithmetic checked; source bridge open |
| 5 canonical private dots | WideExact invariant, redundant-check elimination, outer count implies inner bound, reduction/output | open |
| 6 public decode reuse | checked same-byte decoder/selector correspondence, first_decoded and adapter execution | open |
| 7 geometry reuse | node/denominator agreement, caller range validity, execution | open |
| 10 fixed prefix | admitted q length, identical decoder accesses and failure behavior | open |
| 12 rho residues | every-prefix modular invariant, four-term overflow bound, canonical finish, array/caller execution, heap admission | integer invariant and scalar source bridge checked; push/value emitted and compiled; enclosing loops/finish/callers open |
| 14 Libra factorization | all four weights equal for arbitrary canonical challenges including zero; field/source execution | division-free cut/tensor algebra checked; literal-loop and field/source bridges open |
| composition | refreshed emitted caller bodies, byte/error/effect preservation across tx1/tx2 and adapter | open |
| soundness transfer | apply existing soundness results under their original premises to the actual optimized source model | open |
| privacy transfer | preserve modeled observation/game distributions under original premises; do not claim timing privacy | open |
| release evidence | focused files, consuming bridges, coherent final closure replay and axioms audit; exact source/tool/feature pins and receipts | open |

`CuSavingsResidues` proves the dot and rho integer identities symbolically,
including arbitrary-length rho prefixes. It does not yet establish equality
of an extracted Rust loop. The successful receipt is `residues-e/receipt.json`;
failed attempts are retained and are not release evidence.

`CuSavingsLibra` proves the four algebraic weights after the 28-element runs
are split at the actual tensor cuts, for every commutative semiring and all
challenge values (including zero). The exact twofold loop-to-cut correspondence
and concrete tower-operation bindings remain required. Receipt: `libra-a`.

`AspisR1CuRho.{Types,Funs}` is promoted bytes-unchanged from the push/value
emission; the original full emission is retained under tooling as a diagnostic.
`FunsExternal` supplies concrete map/handback definitions, not the generated
axiom template. `CuSavingsRhoScalar` identifies the newly emitted reducer with
the verified current one, proves checked scalar multiply/add success and binds
the actual bitmask flush predicate. Receipts: `rho-types-a`, `rho-externals-g`,
`rho-funs-pushvalue`, `rho-scalar-a`.

`CuSavingsRhoValue.value_success` proves the complete freshly extracted value
method on every valid Vec index. It performs the actual array map and all four
reads, returning exactly the canonical residues of arbitrary u64 input limbs.
The read-success premise in the intermediate lemma is discharged by the
exported theorem from the index bound. Receipt: `rho-value-c` (standard axioms
only, 1.604 seconds, 2,670,712 KiB peak RSS, no process/cgroup swap).

The full emission's finish path does not typecheck against the pinned runtime:
the emitted mutable Iterator trait supplies a triple including a handback,
whereas the ordinary Iterator interface expects a pair. No generated body was
edited to hide this. Finish remains required; its mutable-enumerate interface
must be modeled/translated faithfully and verified. Push/value was emitted as
a separate focused cone so this interface issue does not hold up its proofs.

The existing unified source manifest check is not a proof replay. The older
readonly-metadata runtime result is not a universal formal premise proof and
is pinned to the older ELF. Neither substitutes for an equivalence theorem.

`CuSavingsRhoPushStep.source_update_step` proves one actual emitted update-loop
iteration, including checked multiplication/addition, both array reads, array
write and the Vec mutable handback. Its premises are local bounds and the
iterator next result; the enclosing four-iteration induction must discharge
these and prove the update/frame invariant. Receipt: `rho-push-step-f`
(standard axioms only, 1.604 seconds, 2,664,852 KiB peak RSS, zero swap).

Next: close the full update-loop induction and flush-loop handback, then
compose them with the already checked every-prefix residue invariant and
canonical value theorem. The remaining candidates and final soundness/privacy
transfer/replay remain required; this checkpoint is not goal completion.
