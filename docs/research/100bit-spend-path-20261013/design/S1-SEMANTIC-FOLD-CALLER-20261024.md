# Concrete semantic round children at preparation and owned stage1

Checked: the unchanged native semantic folds and their retained extracted-loop
references make the same complete ordered arithmetic calls and return the same
four-word result under common arbitrary normally returning children. The
concrete extracted decoder/boundary/value functions are now installed in the
enclosing preparation and owned stage1 theorems; `R` is no longer a free
parameter of these new concrete instances.

**S1 and S6 remain OPEN. Target not yet established.** Native arithmetic/Std/
abort interpretation, actual SDK/account execution and release/security joins
are not proved by this packet. S2 remains transferred. No production source,
artifact, protocol parameter or security metric changed.

## Exact source association

Current adopted source authority remains `25866ec331cc7ce27dd9956609c11d32fa8fa58a`,
including the authorized `29cbab431742f7e899870595167efa193a379f0a` adoption.
The two selected private functions in `r1_semantic.rs` are byte-identical at
historical `b2727acd3abf79315d18b754a260f58f4b1c6326` and that adopted overlay:

- `semantic_boundary`: `24087d364f2f543d7763d940977bf117826767df82207a7fab92f4f59891d5bb`.
- `semantic_value`: `f40e51f1986bab8bd8509dda5f77c97aa455e04e70f8b4503ac8e0f8a5341863`.

Proactive cache/source search located the exact old reference inputs in
`aspis-r1-semantic-calls-root-v5-20261019`. Their complete generated Types and
Funs match the checked `lean/extracted-source-proof-loops-20261019/` owners
byte for byte. The retained Charon/Aeneas receipts, command plans, source pins
and runner hashes agree with those inputs and emissions. No extraction was
repeated. The source-only subset is retained in the new packet, without LLBC
or compiled objects.

The isolated Kani source cut copies the complete private function bodies;
only private visibility is widened inside the proof crate. Its owned-loop
bodies are exact copies of the reference items. The actual `aspis-core` path
dependency is used, with all active local-path sources pinned before and
checked unchanged after verification. Its complete field.rs and wide_exact.rs
equal the adopted source files. No simplified field carrier is introduced.

## Native control checks and their limits

`tools/s1-semantic-fold-20261024/proofs.rs` checks both native and reference
against the same arbitrary full-four-word QM31 output tape. At every add/mul,
it checks both complete operands and the exact call number. The boundary
performs 28 ascending additions, seeded by polynomial[0], including the first
addition of polynomial[0] again. Value performs 28 reverse Horner steps,
strictly multiplication then addition, starting at zero, with 56 calls.
The value harness covers every round in 0..9; `round<10` is explicit.

All 1,008 checks pass, including unwinding assertions, pointer/index checks
and complete output equality. Arithmetic children are stubbed to arbitrary
normal returns. Consequently this is a normal-return control certificate,
not a proof that native arithmetic always returns, a machine-semantics
certificate, or an unrestricted Rust/Lean transport theorem. The harness
does not assume canonical raw words and does not obtain numeric correctness
by executing invalid raw inputs through native arithmetic.

| Target | Checks | Exit | Wall seconds | Peak RSS KiB | Swap |
| --- | ---: | ---: | ---: | ---: | ---: |
| boundary_same_complete_calls, v3 | 442 | 0 | 4.965133 | 601752 | 0 |
| value_same_complete_calls, v1 | 566 | 0 | 108.756372 | 924680 | 0 |

Fresh whole-host `/sys/fs/cgroup` admission ran under the shared flock before
each scope. It includes uncapped VMs/services, rather than scanning only the
user application subtree. The explicit background allowance is 28GiB:
configured guest maxima up to20GiB,2GiB VM overhead,6GiB other services; other
observed uncapped RSS must be at most4GiB. The sum of existing finite caps,
that allowance and the new2GiB cap must remain strictly below55GiB, with at
least10GiB MemAvailable. These service allowances are estimates, not caps on
other owners' workloads. Both jobs used MemoryHigh1536MiB/MemoryMax2GiB,
MemorySwapMax0,TasksMax64; no OOM/memory-pressure event occurred.

The preliminary read-only inspector initially overcounted per-thread RSS;
it was corrected to deduplicate Tgid before the retained preflight snapshot.
That preflight was not admission and launched no job. The actual admission
enumerates only process leaders directly from /proc.

Two setup failures are retained and excluded from accepted proof evidence:
the first metadata probe inherited nightly-only RUSTFLAGS while invoking
stable rustc; no proof ran and no proof timing is claimed for it. The next
attempt compiled but selected an unqualified harness name and failed before
verification (0.129534s,123252KiB,swap0). Clearing RUSTFLAGS only for metadata
and selecting `proofs::boundary_same_complete_calls` fixed these distinct
issues. No unchanged failing proof or larger-cap retry was used.

## Concrete enclosing statements and premise accounting

All new Lean modules are in `lean-candidates/s126-caller-boundary-20261021/`.

`S1ExtractedRoundChildrenV1.children` supplies all three fields with explicit
complete source bodies: indexed decoder, boundary loop and value loop.
Coordinate maps retain all four field words; all decoder Rust error variants
and fail/divergence are preserved. `decode_exact`, `boundary_exact` and
`value_exact` expose these definitions. The native/reference certificates
above do not silently become custom Lean axioms.

Before: `installed_y1_provenance` and `accepted_callback_scratch` universally
quantified over an arbitrary `R : RoundModel.Boundaries`. After:
`S1TopPrepareExtractedChildrenV1.installed_extracted_children_y1` and
`accepted_extracted_children_scratch` use the concrete `children` instead.
Their full accepted op7 call, full carriers, None observer, per-H execution
and conclusions remain the same. This is the required concrete instance of
the generic theorem, not a claim that changing quantifiers weakens every
abstract theorem. No separate child success, codec equality, canonicality or
scratch equation is added as an enclosing premise.

Retained preparation parameters are `base : Ops`, `B : FinishModel.Boundaries`,
`other : Implementation`, `H : Bytes → State`, public/proof/hash/input/output
carriers, and the single same installed accepted-result hypothesis. `B` still
contains fromFn,mask,add,mul,terminal,circle,unwrapRoot,claims. Its concrete
source installation remains a real obligation. `other` handles operations
outside this installed release op7. The theorem retains complete source
effects/result, <=115 reads, exact gamma scratch/callback program, kappa
completion and the actual View.y1/all29-parse provenance through the existing
separate exported conclusions. This is ACCEPTED-ONLY at its parent scope.

`S1OwnedStage1ExtractedChildrenV1.owned_stage1_extracted_children` makes the
same substitution in the complete owned adapter stage1 theorem. Its retained
parameters are adapterOps,ops,B,program/accounts/data/output and one enclosing
owned-stage1 success. Its conclusions still derive the actual decoded public
statement, split, None observer, same prepare/scratch, physical roots,
continuation, View.y1 bytes and all29 field parses. Actual AccountInfo SDK
transport is not supplied by the substitution.

`S1ExtractedRoundChildrenTotalV1` reuses the existing source-loop polynomial
proofs without re-proving S9 mathematics. `boundary_total_canonical` proves
successful complete execution and canonical output for every canonical
28-coefficient array. `value_total_canonical` does so for canonical
coefficient/alpha arrays and round<10. There is no assumed successful helper
call. These are TOTAL on the stated canonical domains, not unconditional
R22 for arbitrary native bytes. Deriving those domains at all enclosing
native reached sites and proving arithmetic/abort/backend transport remain
required; these domain premises have not merely disappeared into a record.

## Validation and next obligations

Four focused local targets passed:138.519197s selected total wall time,
maximum RSS3,989,880,832B,zero swap; all #print axioms reports standard-only.
Smallest changed target was checked first, then changed consumers, using the
atomic local lock,-j1,-M4400 and existing warm objects. The owned-stage1 source was checked once more after removing inherited
whitespace; its original receipt remains historical evidence. Raw compiler
logs and the original receipt source retain their whitespace byte for byte.
Maintained source passes the whitespace check. No unchanged whole
manifest or runtime suite was replayed. Exact source/tool/import hashes,
targets,status,time,RSS,swap and axioms are retained. Import hashes describe
focused cached validation, not a coherent release rebuild.

Evidence: `evidence/s126-current-caller-20261021/s1-semantic-fold-controls-20261024/`,
the four focused Lean attempt directories, and
`s1-semantic-fold-import-pins.json`. Metadata checker:

```
python3 tools/s1-semantic-fold-20261024/check.py
```

Next: connect concrete decoding's reached canonical outputs and sampled
alpha domains into the enclosing source instance; finish the concrete
FinishModel child installations using existing owner proofs; retain native
numeric/Std/abort/effects transport as explicit obligations. S6 still needs
actual SDK/input retention and cross-transaction reconstruction identity,
with the S2 owner supplying its assigned boundary. Final stored-carrier,
release artifact and composed security-experiment joins remain open. No new
production source decision is requested by this additive packet; any later
source/backend change still requires equivalence and re-pin gates.
