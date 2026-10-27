# XRi handoff: external implementations block release association

**Target not yet established. No D188-P2 association or actual-top premise
removed.** Branch codex/cx-extraction-assoc1-20261027. No push/merge. Only this
job's evidence directory is changed; no shipped source, session A worktree,
other worker prefix, ledger, contract, wallet/key or ELF change.

## Established and measured

1. Isolated raw pinned release Types/Funs and both external templates are
   byte-identical to XRh_pinned_outputs_01.json. Host private namespace remains
   XRh_Release, under XRi_generated and outside every main LEAN_PATH. No
   extraction invocation, generated-code repair, alternate producer or axiom
   template is installed. Host library objects are the coherent Lean4.32
   Aeneas base, with direct object and inherited manifests hash-pinned.
2. XRi_L001 is a failed dependency preflight, not a compiler run. XRi_L002 is
   the first Lean invocation using the unchanged S2W command runner: exact raw
   Types target, exit1, wall0.271323047s, RSS865856KiB, swaps0. Diagnostic:
   missing XRh_Release.TypesExternal.olean. It fails before declaration
   elaboration. Funs is blocked transitively, not retried. XRi_ELABORATION.json
   lists all63 Types and297 Funs explicit declarations with their untested
   status. There are zero accepted new theorem/axiom-audit results.
3. XRi_declaration_diff.json covers all132 explicit cohort producer declarations
   and the emitted release declarations/templates. Reused ARX kernel audit
   RPz8_657 has1599 PublicPreparation-prefixed reachable constants mapping to81
   producer declarations; model/proof/other-owner constants remain explicit.
   Reached producer comparison:29 same normalized texts,21 different,5 external
   template candidates,26 without exact-name match. This is source comparison,
   not semantic equality. Source hashes, line references and individual diffs
   are retained. Scratch rejection behavior is detailed in XRi_DIFF.md.
4. Full new Kani allowance spent:10/10;8 PASS,2 CBMC90s TIMEOUT. Public powers
   zero/one at29/7 and split checkpoint writers/all-zero64 weights pass.
   Both distinct sparse whole prepared_claim domains time out. None is rerun
   unchanged; no larger cap, extra run, stub or contract. Full P6 stays open
   for all twelve leaves. XRi_P6.md states domains/limits; every command,
   source/dependency/revision pin and resource result is in its receipt.
   Total Kani wall278.171353192s, peak3670404KiB, swaps0. All optimized, overflow
   checks retained, one compiler job. Private source excerpts' body hashes
   equal immutable release bodies exactly.

## Incomplete requested deliverable and next step

TypesExternal_Template contains three nonstandard type axioms; FunsExternal
contains102 axiom declarations including opaque release leaves and library
operations. They are not missing objects of the pinned Aeneas library.
Ordinary Lean compilation cannot turn them into standard-axiom source models.
No such templates are imported or counted as proved contracts.

XRi_Association.lean is explicitly a comment-only staging file, not a compiled
module with concrete named Props or theorems. Giving it phantom release
carriers/abstract function parameters would replace the requested SAME-source
association with a different theorem. XRi_OBLIGATIONS.md retains every named
proposition specification in XRg order, exact failure/scratch/order conditions
and all twelve P6 statuses. **The requested concrete association proofs are
not delivered.** First supply valid source-associated external implementations,
then compile raw Types/Funs and formulate/prove PreparedScratchProjection.
The two new timed-out sparse claims require smaller arithmetic/Dot stages;
neither timeout establishes falsity.

Lean budget1/100 compiler invocations, plus one preflight. The remaining99 are
unused, not called exhausted: the dependency prerequisite prevents a valid
association target. No attempts are manufactured by repeating blocked files.
Kani budget10/10 exhausted; extraction0. One own capped scope at a time,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000; all barriers
allowed, zero retries, no bypass/cap change/memory kill. No build/launcher
infrastructure source was repaired. Raw source/stdout whitespace is preserved.

## Actual-top statement, ledger and non-vacuity

Full before/after ARX_Root.deployed and Rc10_Top.deployed sources are retained
and hash-identical, matching the inherited XRh baselines. XRi_recount.json pins
top/ledger/contract and records removed/added/changed0/0/0, deltaT0/P0/G0/C0
using atomic quantified families/SAME witness and the L185=L159 alias. No new
absolute recount; no carrier, binder, event, conclusion, metric, game or trust
change. Frozen3, RuntimePersistence and approved game remain adopted.

No joint SAME-witness inhabitant of all actual-top premises is constructed.
Bounded canonical/index domains admit zero/index0; literal powers inputs0/1
are nonempty. Those witnesses are not whole-top non-vacuity. No fresh formatter
reachability or coherent release replay is claimed; RPz8 audit is reused only
with its named scope.

No shipped-file change means no three-ELF rebuild trigger. Historical pins
only, not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Own271030196-byte target and object/.lake scratch removed after recording pins;
no recent solver temp belongs to this job. Older shared temp files untouched.
No binary/object/archive committed. XRi_Verification.json reports no errors.

Stage commits: b18724f56f (isolated preflight blocker),56bb167f6a (declaration
comparison),fe0592916f (bounded checks/remaining obligations), then this final
handoff/verification commit. All local; no push.
