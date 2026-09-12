# Aspis V8 completion task — run, repair and integrate this first-attempt pack

## Objective

Take the user's completed same-body/proof-artifact repair as the local starting
point. Finish as much of the remaining V8 formalisation and implementation as
possible, including **all classical Fiat–Shamir work**, permitted-access payment
extraction, exact security composition, repaired-profile adaptive ZK and resource
closure. Use the code in this folder as first attempts to run and improve, not
as trusted premises or completed certification.

The objective is a correct source-linked theorem with honest scope, not a
successful build carrying a name such as “complete”. Do not stop at the first
failure. Do not compensate for failure by weakening an intended statement,
hiding a conclusion in a structure or adding an axiom. A documented partial
result with a precise next producer is acceptable; an overstated result is not.

## Read first and preserve the completed work

Read README.md, docs/OBLIGATIONS.md, docs/FIAT_SHAMIR.md,
docs/EXTRACTION_ZK_CU.md, docs/TOOLCHAIN_NOTICE.md and config/OBLIGATIONS.json.
The old audit in reference/ is background, not permission to redo or revert the
user's repair.

The authoring environment saw only remote V8 commit:
`30a303a344dbb42e24ad8f42a8804819747942bc`.
The completed local repair was not remote-visible. Do not assume its branch,
commit or API from this old pin. Inspect local worktrees, branches, status and
unpushed commits read-only. Run:

    python run.py --stage preflight --repo /actual/path/to/aspisZK

Identify the actual completed repair producer, independent intended statement,
field/causal map, test evidence and fresh build. Print its full theorem signature.
Confirm that consumed fields come from the same actual body/history and that
causal callbacks do not close over future transcript data. If it already closes
an obligation in this pack, reuse it and mark that obligation satisfied with its
exact producer; do not create a parallel weaker implementation.

Create a new isolated worktree/branch from that local repaired HEAD. Suggested
name: `research/v8-completion-fs-extraction-20260911`, with a safe suffix if
occupied. Never reset, stash, clean, switch or overwrite another worker's tree.
Do not touch V7/main. No merge, push, deployment, on-chain transaction, credential
handling or production-wallet operation is authorised by this prompt.

Record the actual baseline, code/config hashes, compiler/Mathlib pins, exact
import roots and any dirty files. An uncommitted local repair must be frozen as
an explicit source snapshot before it is used as evidence. Preserve its work.

## What is delivered here

The Python tests ran in the authoring environment. Lean, Lake and Rust/Cargo
were unavailable there. **Every new Lean proof is an uncompiled first attempt**;
Rust is uncompiled too. There may be elaboration, API or genuine proof mistakes.
All such errors are your task to diagnose, not reasons to replace the target by
an assumption. The test suite compares some reference algorithms, not actual
Aspis verification or its deployed SBF execution.

Most Lean modules are reusable mathematical/reference-machine components.
Their source-instantiation obligations are explicit. Generic game-hop,
validator-search and probability-ledger consumers are not completed source
proofs. The prime-field decoders and small payment-state model are not the
selected circle/QM31 decoder or full forest/Token payment validator.

Run the portable checks first:

    python run.py --stage python
    python run.py --stage static

Fix any actual failures, preserve logs, and distinguish a bad test expectation
from an algorithm error. Do not edit tests merely because they catch a real
counterexample.

## Toolchain validation: historical pin versus patched kernel

The historical evidence records Lean 4.32.0. Upstream PR14498 fixes an opaque
value free-variable kernel defect; the primary advisory identifies 4.32.2 as
fixed. See TOOLCHAIN_NOTICE. This does not allege an exploit in Aspis.

Keep historical reproduction separate from independent validation. Preserve
the original compiler/cache/logs, then use a separately pinned compatible patched
compiler and Mathlib for the certification build. Do not silently upgrade the
running checkout or substitute incompatible cached artifacts. Verify current
upstream advisories before sign-off.

Resolve the actual existing Lean project from repository configuration. The
runner requires its path and the exact expected version, for example:

    python run.py --stage lean --project "$PINNED_LEAN_PROJECT" \
      --build "$NEW_EMPTY_BUILD_DIR" --expected-version 4.32.2
    python run.py --stage kernel --project "$PINNED_LEAN_PROJECT" \
      --build "$NEW_EMPTY_BUILD_DIR"

Use the true repaired/patched version, not blindly the example. Historical
reproduction has a separate explicit mode in tools/lean_build.py and is not
certification. If external checker/toolchain support is missing, report NOT RUN
or BLOCKED rather than PASS. Do not relax the version policy to make the runner
green without reviewing the actual patch/source evidence.

## Workstream A — literal source refinement

Freeze an independent intended endpoint: actual selected Rust verifier success
on one proof body and authenticated public/runtime context implies the repaired
functional execution accepts or one of the explicitly modelled authentication
failures occurs. The intended statement must use real source success, not a
record defined as ideal acceptance.

Use the completed local repair. Extend it through any remaining mutable-Vec,
byte-slice, integer-range, parser, packed decoder, inverse, scalar-recurrence and
profile-binding gaps. Compare against the exact compiled selected verifier,
not just an older similarly named Rust helper.

The delivered wire.py and Rust Wire parser derive all projections from one
immutable input. Adapt them only after checking the local profile layout. Keep
all 697 fixed fields, both roots, nonce bytes, q22 records and frontiers in the
same identity map. Do not invent a new framing or change protocol acceptance to
simplify a proof.

For the Merkle loop, prove initial guards, paired/single branching, shared
frontier cursor, parity order, exact depth, exhaustion and both root checks.
Preserve original query ordinals across descriptor sorting. Do not let a pure
hash-function value equality substitute for the actual effectful query order.
Use Aeneas/Charon with pinned compatible versions where available. Hand-written
models remain models until an actual source refinement is supplied.

Deliver source-output correspondence for every security-relevant field;
nonvacuity and negative controls; and one producer feeding the previously
conditional functional endpoint. If literal Rust refinement is not done, say so.

## Workstream B — complete Fiat–Shamir implementation correspondence

Read the entire FIAT_SHAMIR plan before writing the global theorem. Fill the
literal transcript bindings from the repaired source; all current nulls are
open tasks, not defaults.

1. Define the exact public statement, context, profile and release serialisation.
   List literal byte strings supplied to each SHA/hashv call. Include counter
   and retry behaviour. Metadata roles never create independent domains unless
   distinct bytes are actually hashed. Audit ambiguous concatenation and
   cross-role identical inputs separately from random hash collisions.

2. Construct the full 256-bit lazy-oracle execution from the adversary's initial
   randomness, code, state and allowed oracle queries. Cache hits reuse prior
   answers. Track first occurrence and all calls, not only the verifier's calls.
   Derive the correspondence with OracleCache/LazyROHazard or reuse a stronger
   already-checked V7 actual-law framework with matching semantics.

3. Build actual chronological C1 and C2 cuts. Prove stopping-prefix locality,
   nesting and answer consistency. Include adversary-first cached queries,
   restoration/fork cursors and exact accepted-trial provenance. An arbitrary
   subset of a full log is not a causal prefix.

4. Prove the exact samplers. Start from full SHA answer preimage counts. Handle
   canonical/nonzero QM31, circle/OOD, second-point distinctness, q22 query
   duplicates/order and all bounded retries. Retain aborts and returned source
   history. Second-sampler laws must hold at every reachable terminal history,
   not merely as an unconditional marginal. Bind scalar data to its actual bytes,
   not a favourable ideal field value.

5. Produce one uniform causal strategy from the same prior source/adversary
   state, valid across all legal continuations. Earlier messages cannot depend
   on later coins; final256 may depend on alpha0. A pointwise post-transcript
   existential ideal execution does not provide probability coupling.

6. Charge named authentication failures with actual resource budgets. Use the
   fixed whole-domain unresolved target sets, a shared raw collision event and
   explicit first exposure. Cached future-chosen targets need their own source
   classification. Do not assume a cached challenge is fresh. Do not assign
   unproved prefix timing or missing source coverage probability zero.

7. Derive the law-preserving or justified game-hop coupling to the ideal
   algebraic experiment. Then instantiate FiatShamirTransport. Its coupled and
   sourceCover premises must have real producers; supplying them as final
   theorem arguments does not close the FS task.

8. Handle repeated/adaptive statements and adversarial restarts according to
   the chosen definition. The lack of honest prover grinding does not prevent
   an adversary from trying many transcript prefixes. State ε(Q,time,instances,
   extraction-budget). Do not automatically carry a ~104-bit per-prefix bound
   into a global 100-bit claim. Do not automatically multiply all terms by Q
   either: establish the actual reduction and count genuine opportunities.

The proposed AdaptiveHazard theorem proves an n·ε union bound for history-
dependent kernels. Its LazyRO instantiation derives the local probability from
pre-answer target cardinalities. Neither theorem identifies the actual Aspis
bad-payment event. That remaining inclusion must be proved, not defined.

Deliver exact source transcript receipts for synthetic fixtures; cross-role
alias classification; full sampler/cutoff/state producers; and the explicit
real-to-ideal coupling theorem. Keep any private witness-bearing log local.

## Workstream C — permitted-access efficient extraction

Separate four claims: algebraic tuple existence, allowed-access candidate
production, decoder correctness/runtime, and full payment-validator success.
Do not equate any of them by naming.

Implement and prove the extractor using the actual frozen query graph or an
explicitly permitted rewind interface. FrozenAccess intentionally rejects
unknown hash inputs. Do not give the extractor a full committed word or extra
opening oracle it has no right to query.

Identify how the existing fixed candidate family is enumerated efficiently.
A classical choice of a family with at most one member is not an algorithm.
If using Gao/error correction, bind actual field operations, the natural-circle
basis, circle-to-GRS map, degree, distinctness, canonical decoding and image
constraints. Use the delivered two independent prime-field decoders as controls.
Do not run their tests and report the selected QM31 decoder proved.

Prove the Euclidean invariant, stopping criterion, exact division, degree,
agreement and uniqueness conditions. Preserve the common sampled corruption
support across all 16 columns. Derive a joint decoder tail from the actual
sampling experiment rather than adding/removing a factor of 16 casually.

For replay/fork collection, preserve the strict common prefix and cached answers.
Count each branch's time, fresh hash queries and repeated work. Record aborts,
censorship and incoherent forks. Prove useful coherent fork production at the
required probability; ForkReplay's deterministic equality is not that proof.

Finally run an independently defined complete payment validator. The bounded
CheckedCandidate search proves only that returned candidates pass its check;
the actual validator's meaning, allowed candidate generation and completeness
remain separate. If the source cannot produce the candidate within budget,
record the failure event rather than declaring algebraic recovery success.

## Workstream D — semantic witness and settlement

Connect the SAME recovered canonical tuple to the exact two-output/24-level
forest relation, not the older V7 one-output/depth-20 witness interface.

Derive ownership, input note opening, directions/occupancy, membership root,
nullifier, asset equality, positive 30-bit outputs, integer conservation, output
pair, append frontier/root/cursor and public afterstate from the actual residuals
and copy links. Positivity follows from the appropriate inverse-product residual
plus canonical/range and arithmetic facts; an equation in a field alone is not
an integer positivity statement.

Bind deployment/program, registry, locked live state, input-history context,
nullifier freshness, account ownership and Token/custody effects. Prove atomic
failure behaviour and exact settlement on the successful path. Keep transfer,
withdrawal and rollover scopes distinct. A successful transfer cannot stand in
for an unexamined withdrawal path.

The provided TransferAmounts and PaymentTransition are small deterministic
building blocks only. They deliberately do not contain fake fields named
ValidPayment or AuthenticatedRuntime asserting what remains to be proved.

## Workstream E — global event ledger and exact arithmetic

Freeze the final adversary/extractor experiment and its independent bad-payment
predicate. Partition the SAME accepted execution and probability space into
charged failures or the actual validated witness result.

Reuse the selected same-Q recovery classification. Do not remove RecoveredHigh
from bad-payment mass until the permitted-extractor/payment implication exists.
Do not substitute different Q, candidate tuple, prefix, statement or profile in
separate branches. Cover empty/absent families, decoder failure, source rejection,
uncovered accepted paths, transcript alias/freshness, and all sampler aborts.

Instantiate the residual bound rather than citing the README display number.
Use exact rationals. Keep the product-root obstruction and its actual sampler
law consistent. The degree90407376 pair expression is around195.14bits; the old
~214 figure concerned a smaller root set and cannot be reused.

The reported103.9998724649bits is a conditional residual, slightly below104.
The supplied decimal rational is only a conservative ceiling of that report,
not an independent formal reconstruction of integratedBudget. Add semantic,
authentication, extraction and FS/resource terms only after establishing their
scope and avoiding duplicated charging. Unknown terms remain null/OPEN.

Output both the symbolic ε(Q,...) theorem and its exact numerical evaluation
at the chosen resource budget. Distinguish success probability, knowledge error
and generic attack-work interpretations. Grinding credit remains zero.

## Workstream F — repaired-profile full-view adaptive ZK

Construct an actual simulator for the intended observer and adaptation model.
Account for all witness-dependent message fields, roots, salted leaves,
ordinary/OOD answers, masks, queried openings, nonce behaviour, transcript hash
queries, aborts and the new positivity/inverse residual.

First derive the actual static mask linear maps, ranks and witness differences.
The shift must lie in the mask map's image for every supported witness pair.
Use masking.py to falsify candidate maps and MaskTranslation to formalise the
uniform shift coupling. This only discharges the linear static slice.

Then handle nonlinear fields and the complete joint adaptive view. A list of
uniform marginals is insufficient. Specify any oracle programming; prove it
is permitted at the chosen point and charge conflicts with prior queries.
Simulation randomness and extractor access must not be conflated. No hidden
witness oracle is allowed. Keep single-theorem versus adaptive multi-theorem
and classical-ROM versus QROM statements distinct.

Do not declare ZK complete based on statistical tests, low leakage on examples,
mask rank alone, or the soundness theorem.

## Workstream G — all-reachable resources and release parity

Pin the actual selected ELF, compiler flags and runtime feature set. Derive
maxima for the full successful transaction: all PDA searches, field/query
retries, frontiers, parser, arithmetic, token/registry/account checks, nullifier
creation, history rollover and withdrawal.

Use CostTrace/cost.py only after source counts and unit-cost bounds are supplied.
The measured1,105,880-CU repaired transfer remains an example, not a universal
bound. Do not silently change canonicality, overflow checking, proof publication
policy, domain sizes or runtime assumptions to fit. Any proposed change needs
its own protocol/profile and fresh security/CU/privacy validation.

Keep the current40,282-byte/q22 architecture unless a real blocker is proved.
If redesign is necessary, preserve the failed attempt/counterexample and compare
alternatives explicitly rather than hiding a new protocol under the old name.

## Independent build, kernel and statement checks

Before promoting any endpoint, resolve exactly one source per first-party
module. Use import_manifest.py with the actual import roots. It rejects
ambiguous source resolution rather than preferring an old cached variant.
Rebuild the relevant first-party transitive closure in a clean output tree.
The pack runner rebuilds this pack only; it does not claim to rebuild Aspis.

Print full theorem types, all implicit/typeclass parameters, relevant unfolded
predicates and recursive premises. Follow every strong assumption to its actual
producer. Check contradictions, empty domains, zero normalisation, hidden
postselection, renamed acceptance and weakened failure events.

Run standard axiom audits and a compatible fresh kernel replay on the patched
validation environment. Check the frozen intended statement independently,
preferably comparator plus an independently implemented checker. Do not count
an import hash log or a successful leaf build as a dependency rebuild.

Preserve conditional lemmas when useful. Do not call them source closure until
their final external source premises are derived. `rfl`, classical choice and
noncomputability are not automatically errors, but noncomputable existence is
not an efficient extractor and constructor projections are not probability work.

## Failure discipline

Work on small milestones, run the focused target, retain each failure and
reduce it. Classify failures as a false statement, wrong representation,
missing source interface, mismatched imported variant, elaboration/API issue,
resource problem or tooling mismatch. Try different proof decompositions and
use existing checked lemmas. Avoid repeatedly rerunning unchanged failures or
only raising heartbeat/memory caps.

Continue independent workstreams when one is blocked, preserving consistent
source pins and accounts of which pieces are executable, compiled, kernel-
replayed, source-connected or merely proposed. Do not ask for clarification
that the local repository can resolve. Do not abandon the task after one error.
Do not bypass safeguards or consume another worker's machine resources.

## Deliverables and completion labels

Commit small auditable changes locally on the isolated branch. No push/merge or
deployment. Include:

- exact baseline and repaired endpoint reused;
- current code and source/dependency hashes;
- intended statements and premise/producer graph;
- literal transcript/call/field maps;
- Lean implementations and all logs;
- source/decoder/FS/extractor/ZK/CU tests and retained counterexamples;
- the complete symbolic and numerical event ledger;
- readable report separating each claim and remaining obligation.

Use PASS/FAIL/BLOCKED/NOT RUN/OUT OF SCOPE separately for source refinement,
chronology, sampler law, uniform FS coupling, authentication budget, permitted
extractor, full payment validator, global numeric theorem, full-view ZK, all-
reachable CU, first-party rebuild, kernel replay and independent statement audit.

A runnable program is not automatically proved. A proved conditional theorem
is not automatically source-connected. A source-connected verifier theorem is
not automatically a global FS knowledge theorem. A soundness theorem is not ZK.

End with the exact new endpoint, what it now constructs rather than assumes,
the strongest claim actually supported, and the smallest remaining missing
producer. Do not supply completion percentages, unjustified odds, or an
unqualified “all done” while a final premise is still externally supplied.
