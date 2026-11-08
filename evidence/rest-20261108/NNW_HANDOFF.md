# NNW Split.rest handoff

Delivered `AspisR1.NNW_Rest.assemble` with exactly
`AspisR1.NNH_Run6Host.RestLaw (Tx := Tx) L0 copy std`.
`NNW_Rest.lean` contains the requested delivered-type equality proved by
`rfl`; L017 checks it and the term. This supplies ONE top field, sp.rest,
and closes no ledger row or deployed security claim.

Branch `codex/cx-rest-20261107`, base `407347e73f2` (merged NNH run6).
Stage commits are listed in NNW_COMMITS.txt; no push.

## Exact statement and assumptions

For all W, Tx, L0, copy, std, adversarial contexts c and native functions
n1/n2: Extraction -> Accepted1 -> Game -> Queries ->
NNH_Run5bSplit.rest L0 copy c n1 n2, at the corrected literal host.
There is no Accepted2, Root0, Realizes, representation, hash-injectivity or
additional success premise. Existing trust inside the approved host/game and
TrustedStd is retained; no trust item is added or reclassified. The field's
quantifiers, carriers and conclusion are unchanged, as checked by rfl.

## Closed components

| Group | Constant in AspisR1 | Passing attempt |
|---|---|---|
| Copy | NNW_Copy.produce | L001 |
| Rc2 events | NNW_Events.produce | L002 |
| Protection | NNW_Protection.produce; six named conjunct producers | L008–014 |
| Trace | NNW_Trace.produce | L004 |
| Recorder | NNW_Recorder.produce | L005 |
| S6N installation | NNW_Installation.produce | L006 |
| Setup | NNW_Setup.produce | L015 |
| Claims and numeric clauses | NNW_Claims.produce | L016 |
| Exact RestLaw | NNW_Rest.assemble | L017 |

Setup and Claims restate the retained NNH producers without the irrelevant
borrow parameter. Claims calls FJp_Residual.numeric directly instead of
projecting a borrow-parameterized Headline. Protection corrects the retained
draft's intermediate-configuration argument and splits the six conjuncts.
No merged module is edited. NNW_FINDINGS.md retains the cap failure L003,
namespace error L007 and own-client retrieval repairs; neither failed term
receives credit. Failed launches were never rerun unchanged.

## Validation and reusable overlay

All successful new roots print only propext, Classical.choice and Quot.sound.
L017: exit0, 35.653078s, RSS 6984136KiB, swap 0.
L018 NNW_COMBINED_IMPORT imports NNH_Run6Combined plus NNW_Rest: exit0,
31.983872s, RSS 6951584KiB, swap 0. This is a focused cached import, not a cold
release replay.

L019 raw ax2 on assemble: exit0, 42.118572s, RSS 7471104KiB, swap 0;
118957 reachable constants, 5699948 edges, zero missing declarations;
walked axioms exactly equal collectAxioms and the same three standard axioms.
The reachable list is retained as .xz plus its original SHA-256.
NNW_validate.py verifies receipts, admissions/limits, sources, axiom sets,
raw equality and the archive. NNW_pincheck.py confirms all 258 selected imported
object paths unchanged; this includes the resolved Aeneas objects/sidecars.
All 16 current modules match their successful source snapshots.

G0 overlay: `/home/dombarker/project-offloads/codex-cx-rest-20261108/NNW_objects`.
Prepend it to NNW_PATHS.json (the exact run6 LEAN_PATH). NNW_EXPORT.json pins
all 16 output objects and their sources; NNW_INPUT_PINS.json pins inherited
source inputs. NNH run6/run5b/SInt2 caches are referenced only, never copied,
moved or deleted. Own objects are retained. The unchanged raw binary is used
by reference and SHA-256 checked. No shipped source, ELF, key or sibling
worktree was changed; the three frozen ELF pins are inherited, not reproduced.

## Budget and remaining work

19/30 scopes: 18 Lean compiles plus one raw audit; 17 pass, two retained proof
failures; scoped wall 562.820801s; maximum RSS 7471104KiB; swap 0. All scopes use
6G high/8G max/swap 0/tasks64, per-file 180s; compiles use -j1 -M7000 async=false.
All admissions exit0 AND allowed:true, share counts<6 and host disk>=40GB.
Zero Kani, extraction, timeout, cap increase or unchanged failed rerun.
NNW_COMPILE.tsv and per-attempt receipts give every section-6 field.

Eleven scopes remain unused because every authorized member is complete:
copy, events, all six protection conjuncts, trace, recorder, S6N, Setup,
Claims, exact assembly, combined import and raw audit each passed. There is
no remaining member to attempt; unchanged green regressions are forbidden.
This is completion of the assigned field, not a contention or budget stop.
A1/A2, unconditional G0/condition(4), NNH-G0-F3 and release/provenance/native/
ELF/cold-replay/Pool/multi-attempt gates remain with their owners, outside this
job; see NNW_REMAINING.md.

target not yet established
