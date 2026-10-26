# SCD handoff: exact admission items still leave observer unassociated

**Target not yet established. L159/L185 remain open.** No SCD_Physical.run_eq,
SCD_Annotation.transport or SCD_Top.deployed is claimed. Branch
`codex/cx-l159-runtime3-20261026`; all stages committed locally; no push/merge.
Explicit residual STOP reached: 3/100 Lean, 0/10 Kani. The remaining budget
was not spent on annotation wrappers or duplicate diagnostics after that stop.

## Proved and residual

1. `lean/SCD_Carrier.lean`, `canonical_stored`, derives the exact canonical
   carrier fact in the SAME oracle world:

       (eval H (canon (lift c P))).output.stored = (eval H P).output.stored

   `stored_iff_observation` proves that the necessary first-pass stored
   projection is equivalent to the following minimal residual:

       forall H run, (eval H runtime).output = some run -> run.accept = true ->
         run.input.stored = (eval H P).output.stored

   `observation_of_first` proves its necessity for any installed verifier.
   None assumes a new runtime law. Stored equality alone is not sufficient
   for full physical public/proof/checkpoint/history/chronological equality.

2. `lean/SCD_ExactTop.lean`, `retained_context`, retains EVERY actual Rc5
   binder verbatim except runtime/binding, including BOTH admissions, both
   accepted wrappers, game fields a-d, RuntimePersistence, extraction,
   syscall, raw join and all bounds. For every such fixed context it constructs
   a runtime violating the minimal byte association AND first-pass equality
   for the exact installed source/configuration. The offline validator checks
   the complete retained source signature against Rc5, not selected names.
   It is an interface/quantifier theorem, NOT a deployed attack or a joint
   inhabitation of every cryptographic premise. Expected unused-variable
   warnings expose the absence of any constraint on that observer.

3. `lean/SCD_Nonvacuity.lean`, `admitted_game_with_unassociated`, includes BOTH
   entry admissions explicitly, SDK/std, BOTH successful native wrappers with
   data1/data2, all four approved game clauses, persistence, nonempty physical
   checkpoint events, and canonical stored identity, simultaneously with a
   mismatching accepted observer in the SAME H. This strengthens SCC's stated
   joint conclusion, which omitted the admissions. CPH's local n1/n2 are not
   the installed crypto/extraction instance. No full Rc5 crypto fixture or
   actual source acceptance is fabricated.

The exact item types explain the residual: RuntimeEntrypointAdmission L e w n
binds native heap/account records to Entry; accepted1/accepted2 fix native
calls on those entries/data slices; game.recorded binds checkpoint bank
Executes traces. None contains the independently quantified ByteProver P or
runtime RunView observer. Canonical lift preserves P's bytes but does not
associate P to the account adversary. Even all the other retained Rc5 types
leave runtime free, as retained_context kernel-checks.

This does NOT challenge the lead's intended physical interpretation or ask
for new runtime trust. The missing fact belongs to the formal construction of
the deployed observer and submission projection from the SAME GExq_/RawJ_
account experiment. Define/instantiate those two binders there and prove their
observation equation using existing admission/wrapper/source facts. If attributed
to existing RuntimeEntrypointAdmission, its current instance carries no such
observer index; the necessary association must be constructed at that boundary,
not asserted for arbitrary runtime/P. Full run equality still also requires
physical public/proof, saved checkpoint/history, adaptive choice and oracle
chronology. ReplayLogLaw is not adopted. No contract or trust change is proposed.

## Before/after and recount

Counted root remains `AspisR1.Rc5_Top.deployed`. Complete source statements in
SCD_BEFORE_Top.lean.txt and SCD_AFTER_Top.lean.txt are byte-identical to the
actual root. SCD_002/stdout.log freshly prints its complete kernel statement,
body and standard-axioms audit. In both statements, L159 is the same
F3T_Runtime.StoredCarrierBinding c D rust P runtime premise; L185 is its
deployment alias. No quantifier, carrier, guard, shared witness, failure event
or conclusion changes. No premise is discharged, added, hidden or reclassified.

SCD_LEDGER_DELTA.json / SCD_validate.py use Rc5's atomic quantified-law-family
method: split conjunctive/structure premises, retain shared dictionaries,
guards and witnesses, exclude output witnesses and identify deployment aliases.
Every scope/class/owner subtotal is re-enumerated offline, including all eleven
approved game clauses:

- Actual: **83T/33P/0C -> 83T/33P/0C; delta 0**.
- Deduplicated deployment-inclusive: **89T/46P/0C -> unchanged**.
- All retained audit rows: **89T/48P/0C -> unchanged**.

## Validation and release boundary

Three focused sequential host invocations used unchanged S2W launchers and
coherent SInt2 objects; no missing dependency build was needed. Every invocation:
`lake env lean -j1 -M7000 -DElab.async=false`, systemd 6G high / 8G max /
swap0 / TasksMax64. Existing JFz hierarchical reservation barrier allowed all
three launches; no waits/retries, timeout, memory kill, raised caps, arithmetic
generation, Rust/Kani/SBF, package or full-manifest replay occurred.

- SCD_001: exit0, wall4.323218179s, RSS5256540KiB, swaps0; revision80e0af6281.
- SCD_002: exit0, wall3.639149235s, RSS5396464KiB, swaps0; revisionaa2a1bd5dd.
- SCD_003: exit0, wall3.235449030s, RSS5333416KiB, swaps0; revisionaa2a1bd5dd.

Each exact dirty source hash/snapshot, target/command, selected direct object
and sidecar fingerprints, errors/warnings, cap checks and full axioms lines are
in its receipt/stdout/time logs. All five new theorem audits and the actual
Rc5 audit use only propext, Classical.choice, Quot.sound. Total Lean wall
11.197816444s; maximumRSS5396464KiB; swaps0. No failed proof is counted as evidence.

SCD_HOST_SOURCES.json matches the three new sources, source/game/runtime/Rc5
owners and both launchers to host bytes. SCD_ADMISSION_SOURCES.json matches
the actual D189 entry/wrapper/admission owner sources. Transitive historical
cache provenance is inherited from SInt2/Rc5/CPH; this is focused cached
verification, not a fresh coherent frozen-release closure rebuild.
`python3 evidence/l159-runtime3-20261026/SCD_validate.py` and `git diff --check`
pass. Final process inspection found no remaining SCD Lean/launcher process.

Only new SCD_ modules and this evidence directory changed. No shipped or
cfg(kani) file, other prefix, session A worktree/candidate, key, wallet or funds
changed. No ELF rebuild trigger. Inherited pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No binaries/objects/archives/ELFs committed. The next concrete deliverable is
the same-account-experiment observer/submission construction and its physical
source refinement. The 100-bit target remains not established.
