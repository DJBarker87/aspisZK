# D594 continuation checkpoint — vertical slice incomplete

Continuation of f9e335854e on codex/pv-stx-20261104. Detailed current claims,
primitive request/answer/mutation/frame/event matrix, reuse provenance and
remaining source associations: [VERTICAL-SLICE.md](VERTICAL-SLICE.md).
The report below this section describes the PREVIOUS checkpoint.

Checked new source work: Rust entropy cleanup/partial-error restoration requests,
full Result erasure through the loop and original account callback, actual
machine exhaustion suffix, nonce sync_directory source continuation, and ports
of the evh entropy/files/runtime and evhB generic allocator/callback semantics.
Local full-answer entropy logs and primitive caller/child substitution follow
ruling(y)'s method, without a new native/Kani certificate. Actual V183 reserve
and RawVecOwner were inspected only. Reuse sources and distinctions are pinned
in reuse-source/manifest.json, verified by check-slice.py --check.

The requested reject→redraw→success/failure slice is NOT complete. Source-local
owner/drop/resource handling, actual nonzero/entropy loop machine execution,
nonce reservation/path/write_all continuation, concrete op12/callback association,
and native terminal still need construction in the SAME world. Accordingly no
source_entry_world, oraclePrefix/countTrace or other deployed projection was
defined. No privacy row/premise was removed, added or changed; T is unchanged.
This is a context handoff with remaining source budget, not completion,
impossibility, checked shipped-source counterexample or budget exhaustion.

Validation:17 new focused scopes91721–91737 (12 successes, five retained failed
source/proof attempts followed by CHANGED sources); no new native/Kani scope,
extractor run, raw audit or full manifest replay. Current24 modules have accepted
objects. New axioms evidence is SUMMARY-BASED, standard-only; historical91799
raw audit covers only its previous42 roots and is NOT an audit of this new
closure. All41 exact preparation inputs retained. New maximum RSS2,691,412KiB,
wall≤3.40s, swaps0; one own scope at a time, 6G/8G/swap0/64 tasks, Lean-M7000.
No new admission refusal/transport failure. host-slice-checkpoint.json verifies
24 current object hashes and an empty own-scope list. No implementation,
soundness, wallet/key change or push. Next focused91738; audits all consumed;
native nextN91801. HANDOFF.md carries the exact next construction and rules.

---

# PV_STX checkpoint: checked fallback substrate, entry still open

Branch codex/pv-stx-20261104; base fd4a644fd414079022f8781c14a6683b41504ab7.
This is a context handoff, NOT task completion or budget exhaustion. Rows removed:
NONE. Privacy target not yet established. No endpoint premise was discharged,
weakened, added, bundled into OWNER, or moved into T. Observer/simulator unchanged.

## Evidence selects B

N91800 is the verbatim CLI help of the retained ae1-2 binary fda587d2...,
whose current hash matches pv-cx2. Its CLI has no state-threading option. Eight
inspected OCaml files byte-match the accepted patch/source manifest. The pure
function effect record lacks state; signature translation only introduces Result.
State-error comments are historical. ROUTE.md, route-decision.json and
translator-source/ contain the complete inspected text, hashes and reasoning.
No translator/source/LLBC modification, new tool or re-extraction was used.
The pv-cx2 identity/regeneration comparisons are reused historical evidence,
not fresh runs. N91800 is CLI inspection only, not a crate extraction.

## Checked, with exact limits

- PV_STX_Code/Machine: syntax for result/call/bind/loop and an explicit typed
  continuation stack. Handler calls take the current world. Only an ok answer
  resumes; failure/div, resource faults, panic/abort and pending retain post-world
  and ordered effects. Cutoff retains a running Config, not a source error/div.
- PV_STX_Composition.two_calls proves the second primitive uses the first
  primitive's POST-world and appends its events. first_fault bypasses it.
- PV_STX_PrefixLaws.advance_add/events_retained/longer_prefix establish machine
  resumption and finite event-prefix retention. Controls.reject_then_success and
  forever_never_returns are small MODEL controls, not deployed execution evidence.
- PV_STX_Fixed.returned_agrees proves the machine's fixed-handler instance agrees
  with Code.denote. It asserts nothing about arbitrary advancing handlers.
- PV_STX_Entropy: six actual extracted declarations lifted into Code, including
  the explicit nonzero/entropy loops, ten reached opaque-call occurrences of
  five kinds, and five pure restoration applications exposed as typed requests.
  generate_erases proves fixed denotation equals the existing extracted
  generate_for_mask_nonce for every original dictionary and nonce.
- PV_STX_Account.callMut_erases/next_erases bind the lifted callback to the actual
  extracted callback, retaining original generic inst/receiver/index/capture.
  Account acquisition and op12 map_err are requests; no eager external Result
  computation is hidden in those nodes. Entropy requests inject into the SAME
  enclosing request family. No whole-helper trace/Result hypothesis was added.

Before: no such syntax/interpreter for these helpers; the older EVH view used
same : ∀ n s, answers n s = getrandom.fill s plus OPEN callee compatibility.
After: these NEW helper definitions have unconditional fixed-denotation equalities;
advancing interpretation is parameterized by primitive world transitions. The old
entry and endpoint premises are unchanged; this is NOT their replacement yet.

## Native/source fidelity still open

No source_entry_world, concrete evh world instantiation, complete primitive
interpreter, native terminal association, RuntimeBinding projection theorem or
actual deployed non-emptiness witness was constructed. The generic handler is
an interface, not the missing concrete native instance. Its fields are not T.
Ordinary finite Result nodes still need transitive native-effect review, and
source stack/thread admissions must be reached operations, including pure paths.
Partial I/O source receiver state, error/rejection cleanup and source drops must
be reconstructed against Rust/LLBC. The pinned translator deduplicates monadic
calls and defaults drops to no-ops; fixed-output equality alone cannot justify
native event multiplicity. These are recorded fidelity frontiers, not a checked
shipped-source counterexample or an impossibility result.

Only OWNER, op227 and op257 may remain as the eventual source-bound conditional
premises. Existing actual source execution/non-emptiness, V400 resource/failure
witness-independence, D520/U/D524, L1/L2 and the separate V370/L3 residual remain.
Next concrete deliverable: source-code lift of retry_attempt and the concrete
prove_masked_attempt closure, then the actual nonce/reserve/material/leaf/opening
callees and op259 sampler continuation, all at one world. No whole-helper run
hypothesis may stand in for any of these definitions.

## Validation, resources, provenance

21 focused Lean executions (91700–91720), including ten retained elaboration/
proof failures, each followed by a CHANGED source. Three audit executions
91797–91799. One admission refusal on 91798 was uncharged, followed by the full
180-second cooldown and SAME-ID retry. One native scope N91800; zero Kani.
All scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000.
Peak Lean RSS across this checkpoint: 4,637,092 KiB; all swaps zero. Every receipt
records exact target/command, exit, wall, RSS, swaps, source revision/blob/hash,
dependency fingerprint and SUMMARY-BASED #print axioms output. Failed logs retain
the elaborator's sorryAx diagnostics and are NEVER accepted or consumed.

The lead released the timing quiet window early (until 1793755157, 01:19:17Z).
N91800 ran at 01:19:31Z; the shim held it until release. This job never edited
or bypassed the marker. quiet-window.json records both observations.

The 5,673 external objects match h4 authority d9187c80... before compilation.
Effective namespace-first resolution and selected project source/object hashes
are retained per preparation. Existing objects were reused read-only; no library
was rebuilt. NDR's known incoherent cohort was not used.

91799 uses Stream A's BYTE-IDENTICAL NEP walker and its private importAll driver
(changes only module filename and root arrays). All 42 roots complete, zero
unresolved constants, every raw set equals its cached summary and is a subset of
{propext, Classical.choice, Quot.sound}. raw-audit/ contains all reachable lists
and hashes. This checks the CURRENT substrate/helper closure only, not the absent
full source entry or privacy endpoint. No unchanged full regression or full
privacy release replay was run. validation.json and the syntax generator --check
pass. Audit tool sources/changes and retained planted-case provenance are pinned.

All build sources/objects are retained in the private host directory for the next
source work. No binaries/oleans are committed. No crates/, programs/,
tools/r1-cost-probe/, soundness files, wallets, accounts or keys changed. No push.
See commits.txt for git log --oneline fd4a644fd4..HEAD before the evidence commit.

All 24 exact preparation inputs are retained in preparations/. Eleven overwritten
inputs were recovered deterministically and accepted only when their bytes
matched the ORIGINAL receipt SHA-256; recovery.json records provenance. No
compiler was rerun to recover evidence. The final retained object hashes and
absence of own live scopes are recorded in host-checkpoint.json.
