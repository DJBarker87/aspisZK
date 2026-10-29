# D476: Result fibres on the charged complement

Verdict: **NOT RESOLVABLE for the existing Result-only installation**. The
source-level obstruction is the exact `prove_wall_seconds` value in the
successful client's returned JSON and stdout. An event-retaining interface
is an owner decision. The headline, simulator, observer, bound, frozen Rust,
and trust list have not been changed. Target not yet established.

This is a source/control-flow finding plus checked generic Lean theorems,
not a claimed paired native non-bad execution or a complete native
reachability/termination theorem. In particular no unproved actual-run fibre
law is introduced as an assumption to obtain a favourable conclusion.

## Exact domain and quantifiers

Fix the headline's actual template, outputs, statement x, adversary adv and
honest witness w with h.public w = x.1. Use exactly its local W, Pr, h, B and
source, not a different wire or retry experiment:

```
old := QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w
queries := PrivacyR1HeadlineDeployedReal.realSeedQueries
  template outputs x rust observer_program adv w
```

For the **same common sample** s of the proposed RunJoin coupling cp, write
`cp.toM s = ((m, seed), tape)`. The required complement is exactly:

```
¬ ∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s)
```

`PV_FIB_Restricted.offCharged_exact` proves this equivalent to all three:

1. `∀ i, ¬ old i m`;
2. `¬ ProverCommitSeedEvent19.seedGuess (queries m) seed`;
3. `∀ j, ¬ ProverCommitFuelJoin22.failure j tape`.

`realBad` is `parserBad` of the selected eight Q22 answer blocks, including
the real-vector association. Seed queries are the headline's adversary-only
source suffix, not the entire native call log. Fuel failure is the fixed
auxiliary tape's exhaustion event, not the predicate "the native process
failed" or "all retries rejected". Lazy collision/freshness estimates used
in the mass proof do not add a license to discard arbitrary native runs.

A reachable runtime execution is required if it has **any** good common
preimage: `{ cp.toR s | OffCharged old queries (cp.toM s) }`. It is invalid to
exclude it because another preimage is bad, condition on acceptance, or
replace the actual common-sample association by independent coins. Native
association of these coordinates remains an explicit owning-line obligation.

`PV_FIB_Restricted.Required` is a Lean Prop using that exact complement,
`SourceFibres`, the actual returned Result including the success world, and
`PV_RJ4IDB.actualObservation`. Its `I` ranges over all common samples of all
admissible invocations, including different witnesses. Pairwise requirements
are: both samples good, identical public input and adversary/public policy,
identical option-B signal, identical returned Result imply identical COMPLETE
observations. No restriction to the same witness, success, or prefix is made.
The public function must contain only genuinely public invocation data; it
cannot be instantiated with coins, witness, timing, or the desired trace.

By `result_fibres_exact`, in each public/signal stratum these are precisely:
same value **and** final world on successes; same error on failures; and all
divergent finite prefixes. The full ordered event list, not just channel
marginals or decision bits, must agree. `decoder_implies_fibres` and
`fibres_imply_decoder` prove necessity and sufficiency of the generic fibre
condition for a decoder on the good domain. Thus the Prop does not silently
weaken what RunJoin.agreement/test_bound consume. Fibre adequacy alone still
does not prove the decoder's off-bad equality with the model experiment.

Option B makes a proved witness-independent environmental failure signal
public to both experiments. This is not permission to declare the entire
prefix or clock reading public. Existing Runtime does not yet have a
separate signal argument; installation also needs a public-signal association
or its recovery from existing arguments. The success obstruction below uses
the identical no-failure signal, so that issue cannot repair it.

## Successful-path obstruction

Frozen `tools/r1-cost-probe/src/bin/devnet_spend/plan.rs` (r1p-check arm):

- line 84 obtains `started = Instant::now()`;
- line 116 obtains `result` from `RealR1_client::prove_for_proof_accounts`;
- lines 117–128 select the account, write proof.bin/statement.bin and build
  the settlement/publication data;
- line 129 inserts `started.elapsed().as_secs_f64()` into JSON under
  `prove_wall_seconds`;
- `devnet_spend.rs:15` prints the returned JSON to stdout.

The wrapper bytes equal the retained successful client build-03 source.
The feature check is r1p-check; enabling ct-host-prover suppresses internal
CHECK_TIMES but does not suppress this wrapper clock read.

Take any completed honest success outside the three charged events. Hold
fixed public input, witness, initial state, all entropy/oracle replies,
publication step, final core State, filesystem contents and successful I/O
outcomes. Compare two successful schedules which differ only by a finite
pause immediately before the post-computation `elapsed` read. Choose a
pause large enough to change the serialized finite f64 seconds value. That
read occurs after every operation determining the core returned Output. It
changes no query, seed, tape failure, error, or option-B signal. It changes
`prove_wall_seconds`, hence JSON/stdout bytes and the complete ordered
observation. The same core Result and public data therefore cannot determine
that observation, including on the charged complement.

This is a scheduler/clock influence argument about the frozen native source,
not evidence that wall time leaks the witness, and not an abstract arbitrary
Run pair promoted to native reachability. The interface demands functional
recovery, which is stronger than witness independence or simulatable timing.
`post_clock_obstruction` proves the generic impossibility for any one good
completed path with two retained post-computation readings;
`component_obstruction` lifts one differing projection to the full fibre.
The checked source establishes the clock's location and sole influence;
compiler preservation stays at the existing V370 boundary. No native paired
measurement or certified non-bad coin assignment was manufactured. Existing
client success fixtures show execution, not an off-bad certificate.

The abstract State parameters N/L/C are free data. They could be redesigned
to retain the observation/clock completion, but no such deployed association
is supplied, and the existing execute computation ends at the retry client.
Putting the future wrapper observation into State/Result would be an actual
interface/composition change, not a proof of these existing fibres.

Files, publication fields, attempts and oracle history still need the named
acquisition/publication/order/codec links in the earlier LINKS.md. No claim
that they all factor was made: one concrete retained field already prevents
the complete success theorem. In particular keeping only final file contents
would not establish equality of ordered create/write/sync or partial writes.

## Failure and divergence classification

| Source class | Charged? | Required public/prefix association and present status |
|---|---|---|
| Bad account/ABI, malformed public request, wrong public master/lane/checkpoint, unsupported variant | Not automatically | Public input guards; prefix is the public guard path up to environmental effects. Source guard order is visible. This does not classify later private `Semantic` failures as public. |
| getrandom error, allocation failure, ledger open/create/write/sync, proof/statement write failure, stdout partial/failure, process panic/abort | Not automatically | Option B/rdea-1 retains the public failure signal. Witness independence of the selected event and full prefix/order association remain obligations. A shared error label alone cannot determine partial writes or prior oracle calls. |
| Repeated-zero entropy rejection | Only if identified with the SAME fixed-tape `failure j` | The entropy routine has a finite retry limit. Its source-to-tape/status association is required; `Error::Entropy` also merges OS errors. These must not all be charged as tape exhaustion. |
| Selected Q22 parser exhaustion | Yes, if the named actual-vector/source association identifies it with `realBad i m` | This is the exact old charged event; off it this particular failure is impossible. |
| Mask/field rejection-sampler exhaustion | Only where the existing source/fuel or old-event link proves containment | Frozen `mask_error` converts MaskSampleExhausted into Rejected with r1p-check. This is not definitionally Q22 parserBad. Cannot discard without the precise existing event correspondence. |
| ActivePole or `P_R1` rejection | Not by the displayed `realBad` definition alone | Frozen `semantic_error` and `public_check` return Rejected; honest model/source semantic links and retained prefixes still required. They may be finite honest rejects on the good domain. |
| Eight Rejected outcomes / AttemptsExhausted | Not blanket charged | Retry cap gives termination of the control recursion, not containment of all rejected attempts in realBad. No theorem equating this error with auxiliary tape exhaustion is assumed. The full honest failed prefix remains to associate, even though no proof is published. |
| Reused nonce / durable duplicate | Not automatically | Nonce policy and existing ledger are public; reservation is before masks. The existing same-public-ledger coupling must preserve the failed operation/prefix. A Semantic label merges this with other causes. |
| Other Semantic/Layout/invariant errors, Parse/Transcript/Relation/Merkle/Query/Checkpoint propagated errors | Not automatically | Public precondition failures must be separated from internal invariants. Honest-correctness/source laws must exclude internal cases or prove their complete public prefix. The arbitrary Runtime body does not provide these facts. |
| Aeneas outer `.fail e` | Not automatically | World and calls are erased. Conditioning on the option-B signal still requires equality of all prior calls on each signal stratum; no such theorem follows from Result equality. |
| `.div`, blocking I/O/entropy, starvation or external termination | Not automatically | Finite outer fuel cannot exclude a nonreturning callback or system operation. Public environmental treatment and finite-prefix association remain explicit; no new “divergence bad event” is introduced. |

`PV_FIB_Termination.run_not_div` proves finite retry recursion cannot diverge
**provided every entered callback is non-divergent**. `zero_fuel` returns
`.ok (.stop .AttemptsExhausted,state)`. The actual callback is still an
external/source body and its global termination hypothesis is not discharged
here. Thus there is no unsupported assertion that honest native runs off-bad
all terminate. Similarly, a finite retry count does not make failed prefixes
public. These are precise retained obligations rather than additional T
fields. They cannot salvage the independently failing success fibre.

## Premise delta and owner action

Removed from the deployed headline: **none**. Retained: the sole
RustRealRefinement premise, the earlier LINKS.md native acquisitions/source
associations, and the three-field trust list. Added to the headline or T:
**none**. The generic theorems take named ordinary arguments, not axioms.
No original module, soundness ledger, crates/programs, release artifact, key,
wallet, or other worktree was edited. No push or merge was performed.

Next concrete deliverable: owner chooses an event-retaining Runtime/Result
completion boundary that includes the actual wrapper clock/stdout and the
ordered failed/divergent prefixes, then owners supply its native association
and fixed codecs into View/oracle carriers and recompose the unchanged
headline. Merely reclassifying elapsed time as public input, replacing it by
zero, adding it to the option-B failure signal, or assuming V038 agreement
would change the question. D166 simulatable timing is a separate distributional
route; it does not prove Result-fibre functional recovery.

## Validation receipts

Focused targets use inherited Lean 4.32 (`8c9756b…`), -M7000, one scope at a
time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Admission
checked allowed:true AND exit 0 in the command launching each scope. Exact
commands, source revisions/hashes and original `#print axioms` are in each
receipt; original output/time/admission logs are retained alongside it.

| Attempt | Exact target | Exit | Wall seconds | Peak RSS KiB | Swaps | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67500 | PV_FIB_Restricted | 1 | 1.64 | 4165316 | 0 | e90d65ab443428fb2a01ed7ce89d73b48c89f3f8 |
| 67501 | PV_FIB_Restricted | 0 | 1.69 | 4187208 | 0 | 2503a4985e70b94788e9fbe14b7d3dc5918d26a0 |
| 67502 | PV_FIB_Termination | 0 | 1.73 | 4269336 | 0 | 2503a4985e70b94788e9fbe14b7d3dc5918d26a0 |
| 67503 | PV_FIB_Restricted | 0 | 1.73 | 4189484 | 0 | 5a03e06971cedec98fee0a8d8951a54cdd1f6e67 |

67500 was a parser failure: `public` is reserved in the pinned Lean version.
The replacement renames the binder `pubData`; no failed source was retried
unchanged. 67503 adds decoder sufficiency and the explicit common-sample Prop.
The subsequent final edit indexes old/queries by invocation so that comparing
different witnesses does not accidentally use one witness's charged event.
Its focused receipt is listed below after completion.

Axioms audit: offCharged_exact and fibres_imply_decoder use only
[propext, Classical.choice, Quot.sound]; all other new theorems use none.
No sorry/admit/axiom/native_decide/implemented_by, recursion/heartbeat override,
or broad arithmetic reduction was introduced. There are no generated
certificate chunks and no changed generic recurrence. No unchanged full
regression, endpoint release replay, Aeneas extraction, Rust build, or Kani
run was launched. Source checks and Python syntax checks pass.

Reuse: the two prepare manifests independently verify the actual inherited
LEAN_PATH/toolchain and object hashes before loading them: 599 and 912 project/import
checks respectively and all 5,673 external objects against the coherent privacy replay
manifest retained as pv-rj4id's external-authority.json. Each recorded project
source is compared to its selected EJR/frozen/read-only runjoin/HEAD source;
recorded import edges are checked against the objects actually resolved.
Only own sources/J.json/evidence are written under
/home/dombarker/project-offloads/codex-pv-fib-20261029; other jobs' objects are
read-only. No cache is rebuilt or overwritten. Earlier prepare input errors
(missing current-tree manifest path, corrected to the committed retained
manifest) launched no compiler or scope.

Budget stop is the checked frozen-source post-result clock influence, not
budget exhaustion. No unproved whole refinement or new trust field is used.

Final focused result: **67504 / PV_FIB_Restricted**, exit **0**, wall
**1.78 s**, peak RSS **4,189,436 KiB**, swaps **0**, source revision
**22a64ad26f83fea721798ddbe382127c93093730**. Its five axiom lines are in
receipt-67504.json/out-67504.log; only the standard three axioms occur.
Together with unchanged accepted 67502, this is the final own-source
manifest. `final-check.py` verifies the current source hashes and every new
theorem's axiom report without repeating an unchanged Lean build.

Budget used: **5/100 Lean attempts**, **0/20 native scopes**, **0 Kani**.
Audit IDs 67597–67599 unused; all launches were 67500–67504. All successful
modules already include their complete `#print axioms` audits.

Branch: codex/pv-fib-20261029. Base: 5e94f9d425. Work commits before this
final evidence commit:

```
22a64ad26f Index charged events by invocation across equal-public witnesses
5a03e06971 Specify common-sample fibres and prove decoder sufficiency
2503a4985e Use an identifier accepted by the pinned Lean parser
e90d65ab44 Separate finite retry control from callback termination
a12f2fb62d Prepare focused fibre check against pinned inherited cohort
02c29b26b9 State exact charged-domain fibres and post-clock obstruction
```
