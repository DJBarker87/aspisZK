# S10 owned-adapter re-pin — 23 October 2026

## Stage 1: adopted artifact reproduction

Compiler input revision `d50042542971c7a11bab8c3662896ccf834daa59`.
`source-inputs.json` pins all 7,978 retained workspace inputs. Relative to
S10's 22 October snapshot (`7acf5cfb5fa49f4cf5d8e69566ba8221189c31ac`), five
files change: three `r1_pool_adapter*.rs` files, test-only `lib.rs` wiring
and `adapter_rw_tests.rs`. `source-delta.json` records the exact deltas.
The child source inputs are unchanged. No shipped file is edited by this task.

Build receipts and artifact comparisons are retained in `build-manifest.json`.
Each optimized SBF build uses its own MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 scope and `-j 4`. Time is expected in optimized
compilation and MIR/LLVM/mono diagnostic emission, not finite-field elimination.
Platform tools are v1.52, with the retained features and devnet program IDs.
Raw compiler stack-frame diagnostics remain visible: artifact reproduction
alone is not a runtime safety or semantic refinement claim.

Two unsuccessful setup attempts remain recorded. Default-v2 failed before
compilation because the copied diagnostic wrapper lacked its executable bit;
restoring that mode allowed default-v3. Devnet-v1 was launched too early and
was stopped while Cargo waited for the private target lock (no devnet crate
compiled). The replacement launcher holds a private workspace lock through
artifact and diagnostic capture; devnet-v2 then runs after default capture.
Neither failure was memory pressure. No cap was raised.

The reused receipt harness writes historical revision `b2727acd`; this is
not the compiler input revision. `build-manifest.json` explicitly corrects
that field using the independently rehashed snapshot, retaining raw receipts.
No binaries, objects, tarballs or wallet keys are committed. Cargo-generated
keys stay securely on the private host; no keys are cleaned up.
No Lean process is started. `#print axioms`: N/A for this compiler evidence.
Historical pass 1–5 and 22 October certificates remain untouched.
S10 completeness and S2 caller identities remain open; target not yet established.

All three successful builds reproduce the adopted pins:

| Mode | SHA-256 | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| default | `d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0` | 34.960 | 686600 | 0 |
| devnet | `2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922` | 35.499 | 686536 | 0 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 34.962 | 676788 | 0 |

## Stage 2: regenerated ELF/compiler/ordering evidence

The same pass 1–5 algorithms regenerate ELF graphs, raw symbol aliases,
independent LLVM disassembly checks, forty frontier observations per mode,
typed-instance observations and callback flow. `generator-adapters.json`
identifies original scripts and the path/hash/build-label adaptations.
An initial collector referenced the failed devnet-v1 directory, and initial
packet preparation lacked its output directory. Both failures, exact scripts
and resource receipts remain retained; changed path/setup scripts replace them.
No SBF build was repeated for these Python path corrections.

LLVM confirms all 1,633 verifier calls per mode (previously 1,603) and all
2,202 Pool calls. Indirect counts remain 36/36/80; relocated code-pointer
candidates remain 17/17/26. No final DWARF inline map is present. Full call
instruction tables, aliases, relocations and direct-entrypoint reachability
lower bounds are retained, without inventing indirect edges or inlined-source
reachability. Large typed-instance output remains hash/size-pinned on the host.
The callback replay preserves 15 constant SHA targets, six null observers and
131 open library sites; all 189 negative controls reject.

All **140** retained selected-call dominance facts survive, with **zero
re-selections and zero changed block coordinates** against the 22 October
re-pin. All twelve nonempty CFG edge lists are unchanged. The two
process_r1_cost_probe_instruction facts have changed raw MIR body hashes due
to SDK/type pretty-printer qualification; the selected call keys and cuts
match after explicit alias normalization. `ordering-repin-map.json` retains
every old/new fact/header/body pin and independently checked cut. The owned
stage1/stage2 caller is outside these 140 child/wrapper facts: no new caller
ordering is inferred from their preservation. Generic Lean graph mathematics
is reused at its old scope; no Lean specialization or source/model execution
identity is proved here.

## Stage 3: exact declaration/instance/edge delta and ownership

Comparison baseline is the immediately previous S10 re-pin, not pass 1.
`mir-diff.json` lists all 193 changed signature groups per verifier: 111
added, 81 removed and one same-signature raw body change. All belong to the
program crate; core, statement and verifier generic bodies are unchanged.
The supplemental explicit-alias comparison (`alias-mir-diff.json`) matches
76 groups whose body text changes only by aliases/source coordinates, leaving
34 added owned support groups, four removed caller closures and two replaced
stage bodies. These 40 groups are all adapter caller/glue declarations.
Old/new raw signatures, hashes, inline scopes and call operands are retained;
normalization is never substituted for semantic equivalence. The first alias
comparison and its exact residuals are retained as historical diagnostic data.
The final version adds individually listed statement/SDK qualification aliases.

Every one of the 32 exact mono-record deltas, 94 LLVM emitted declaration/
definition text groups, 309 ELF symbol-name groups and 97 endpoint-name edge
multiset deltas per verifier is listed in the corresponding `*-diff.json`.
Symbol aliases and duplicate same-name instances remain separate records;
addresses/layout are not guessed equal. Pool has zero deltas in every view.
`call-alias-audit.json` explicitly distinguishes raw symbol-alias call records
(1,640/1,640/2,220) from physical instructions (1,633/1,633/2,202), and raw
callx records (37/37/81) from physical callx instructions (36/36/80).
All duplicate-site instruction records agree exactly.

The narrow substantive **source/project MIR** delta is adapter caller glue.
All 27 top-level helper cuts in the byte-identical pre-stage prefix are
individually pinned in `child-pins.json`, in addition to the unchanged child
workspace files. The whole source diff also includes test wiring/tests, and
the machine delta is not literally only adapter files plus inlined code:
new out-of-line `ProgramError::clone` and `String::clone` functions are emitted
for the owned caller's library support. Those library call edges are listed
separately in `change-assessment.json`; other changed edge callers are the
old/new adapter. Raw ELF instruction hashes also change with relocations and
layout. No child-source or child-generic-MIR semantic change is observed.
This is compiler/source evidence, not a compiler semantic correctness proof.

`inventory.json` contains 1,046 nonzero ELF symbol occurrences with one
proposed owner or existing library boundary each (zero unassigned/double).
It retains direct-entrypoint reachability lower bounds and all open callx
sites, not a complete deployed reachable/inlined declaration set.
`declaration-ownership.json` pins 14,249 emitted generic bodies
(4,664/4,664/4,921) and their host-only 8.7 MB ownership JSONL.
The full 32.2 MB MIR calls/inline census also remains host-only, hash/size-pinned.
The lead's 161-record ownership overlay is retained at its actual proposal
scope; new compiler IDs are regenerated. Owned caller/glue inherits S2;
first/first_decoded retains S6. New library support keeps the existing
library-boundary proposals; no trust item is introduced or discharged.

Both `inventory.py --check --require-complete` and
`reconcile.py --check --require-complete` still exit **2**.
S2 caller identities, final inline/source correspondence, owner acceptance,
concrete source Calls tree/carriers, source_order/model_order and the coherent
final release replay remain open. No headline premise is removed.

## Stage 4: dated inventory and focused integrity audit

The 23 October S10-INVENTORY section records current pins, historical scope,
all ordering facts, exact delta counts, ownership and the out-of-line library
support qualification. `audit.py` checks current source/output/generator pins,
all scoped resource receipts and reservations, the independent CFG cuts and
bypass mutations, callback replay, alias consistency and deterministic gates.
`validation.json` records its target, revision, exit, wall, peak RSS, swap and
N/A axioms status; `final-pins.json` binds final scripts, inputs and report.
This focused Python audit is not a frozen-manifest or formal release replay.

No Lean theorem is added or compiled, no unrelated runtime/adversarial suite
is repeated, no task build scope remains running, no key is removed and no
push occurs. The headline target and all remaining source/execution joins are
unchanged. Both completeness gates remain exit 2; target not yet established.
