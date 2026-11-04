# PV evhB allocator/callback context checkpoint

## D580 shared Vec resume from c1b31fa688

Read `../../SHARED-VEC-D580.md` and `shared-vec-D580.json` alongside the blocker.
Generic native reserve/push correspondence NOT established; header delivery
and the exact v263 D579 value-erasure equality remain OPEN. No reached-state
counterexample found. RawVec source hashes match across the slices. Source
inspection identifies the actual pointer/capacity commit and push store/length
ordering, but the source-bound owner/call lookup and its preservation are absent
from the inspected interfaces. V183's returning Option-pointer step also does
not supply the generic interpreter's nonreturning native outcomes. Do not install
a model hook or last-history metadata lookup as a substitute for this proof.

Stopped under the inherited blocker/focus rule. Memory fidelity and actual
advancing loop/new/move/entry world delivery still depend on the missing native
instance. No source/axiom/endpoint weakening or new T field. No compile, host,
native, Kani, extraction or new axiom audit. **NEXT91222;74 attempts remain**;
Audit91298–91299 untouched. Historical accepted sources and receipts unchanged.
The earlier checkpoint below remains historical; the new shared document is a
specification and inspection report, not an accepted theorem. The missing
inherited `prompt-pv-evh4.txt` is still absent; no contents were invented.

## D580 resume stop

Read `../../BLOCKER-evhB.md` and `resume-D580-blocker.json` before resuming.
Inspection at b5854a3a17 found no reached native instance proving post-reserve
metadata delivery from `Execution.buffer` to `runtime.metadata e.world v`.
Stopped under the user's explicit blocker rule. No proof/source change or
compile/native/Kani/host run; accounting below is unchanged (next91222,74 left).

Continue ONLY `/Users/dominic/ZK/.worktrees/pv-evhB`, branch
`codex/pv-evhB-20261103`, base `034dfee6ac`. New sources use `PV_EVHB_`;
never edit/restage accepted PV_EVH or PV_EVHB sources. No push/delegation,
Rust/program/soundness edits, native run, Kani run or key/funds action occurred.
No endpoint/deployment row removed; T unchanged; target NOT established.

## Final checked state

23/97 attempts charged: **17 accepted / 6 rejected; 74 REMAIN**.
Normal91200–91221 are consumed. **NEXT NORMAL ID91222**.
Final scoped Audit91297 passed; Audit91298–91299 are untouched and consume the
same remaining74 budget if used. Do not reuse any submitted ID. Three uncharged
reservation refusals at91221 observed the full180s cooldown from each latest
refusal before retrying the SAME unlaunched ID. Fourth admission compiled once,
exit0. No other refusal, transport failure, timeout, kill or cap rise occurred.
No WIP proof or pending compile remains. host-final.json confirms no own active
scope. Receipt audit and adopted source-binding --check PASS. Peak RSS is
4,435,388KiB; swap0. Exact targets/exits/walls/source revisions/object/dependency
hashes and all axiom prints are in the per-run receipts and logs.

All17 new modules (including Audit) are accepted and immutable. The final Audit
was one scoped import/summary-axioms check of the16 proof modules, not a raw NEP
walk, full endpoint/frozen package replay, runtime test or release certification.
Source-level six caller transports, PrivateSaltsNew and all public-size laws
are now green. `summary.json` is the machine-checked accounting authority.
This is a CONTEXT CHECKPOINT, not budget exhaustion or a target-completion
claim. Final evidence/checkpoint commits follow the saved commits.txt list.

## Checked deliverables and exact limitations

Read `FRONTIER.md` and `source-binding.json`. All source modules are standalone
under `lean/`. `commits.txt` gives the base-to-HEAD list before final checkpoint.

- CallbackEffects, CallbackSelection and CallbackOutcomes give full ordered
  argument/capture destruction and Result/fault/div/exhaustion laws, with exact
  states/events and unused-capture branches. Typed constructors replace the
  generic map_err slot in MaterialFromEntropy, ApplyMaterial, PrivateSalts,
  PrepareOpening, PublishCompact and PrivateSaltStep. All six caller source
  transport theorems are accepted. Actual native destruction association stays
  open; generic primitive drop views are not native adequacy proofs.
- ValueMap supplies complete map outcomes; PrivateSaltsNew installs the final
  PrivateSalts::new callback using typed new/move effects (both source checking
  statuses must be read from receipts at resume). Native moves/ownership and
  the zeroizing PrivateSalts destructor remain open.
- ReserveWorld connects the SAME pinned V183 execute/selectedAt family to Q,
  returns the full allocator post-world to its continuation, exposes history
  and result events, and retains allocation denial/overflow. `public_metadata`
  proves that equal address/capacity/length and initial allocator world give
  equal allocation outcomes and worlds independently of element values.
- SaltsReserve factors the ACTUAL extracted prover body and substitutes V183
  at its first reserve; the request uses FIBRE_COUNT and Vec::new, and byte size
  is public count × element width. This does not bind native metadata/width.
- PublishInstall/PublishWorld install CapacityWorld in the actual source-shaped
  publication body. `initial_denied` retains the public-count event prefix,
  allocator state/errno and denial diagnostics and stops before MAGIC.
- WorkerRequests proves public partition lengths/bounds and source-indexed
  potential explicit capacity/byte requests. This is not temporal arrival
  order, std::thread/TLS/collect's complete request set, or the realized prefix
  when a worker panics/diverges.

V183 Kani source credit stays SUSPENDED(K-3), per runjoin73 D564. The three
reused modules are ReserveWorld/ReserveSelected/AllocatorWorld63 in namespace
R1Z.PV_FXM / R1Z.PV_RunJoin, resolved from the SAME runjoin32 instance. Exact
source/object/dependency/external checks are in allocator-extension.json.
No shared source/object or library/LEAN_PATH/J.json was changed. Only three
hash-checked plain object/companion copies were added to the pinned own overlay.
This is not a raw full-data cohort-coherence audit.

## Next substantive deliverable

Thread ReserveWorld's returned world through the actual salt loop and the
new/move continuation, then through the original native prover entry. Do NOT
discard it to fit an older Q leaf returning only a Vec, and do NOT use a supplied
whole-helper Result as execution. Close the source metadata/capacity/layout,
Global/System ValidAnswer and physical same-memory/owned Vec/Box associations.
V183.step is a total Option-pointer model: it does not supply nonreturning
allocator/OS failure/abort behaviour by itself. Such runtime WORLD delivery,
and encoding/native observation association, remain exact adequacy obligations.

V400/rdea-1: initial allocator-world/answers witness-independence; later request
sizes/count/order and failure timing. V400/rdea-2: advancing thread/TLS/join/
worker-panic/exhaustion/scheduling world at op257/host_work.map, with failure
occurrence/timing witness-independent or precisely named. Public ranges do not
prove those facts. Preserve source panic=abort, diagnostics/hooks and every
failure prefix. V370/L3 physical moves, captures/registers/spills/drop glue and
zeroization remain; no new T field. Then full actual-family trace projections
and the (v-prime) non-emptiness witness, with all D520/U/D524 conditions intact.

## Reproduce and account safely

Use ONLY new target sources, committed before staging:

    python3 tools/pv-evhB-20261103/stage.py PV_EVHB_NewModule
    python3 tools/pv-evhB-20261103/compile.py NEXT_ID PV_EVHB_NewModule

Pinned host workspace `/home/dombarker/project-offloads/codex-pv-evh-20261029`;
runjoin32 cohort. One scope only, MemoryHigh6G/MemoryMax8G/swap0/tasks64,
Lean-M7000. Same-shell admission requires exit0 AND allowed:true. Refusals are
uncharged: wait at least180s from latest refusal epoch, retry SAME unlaunched
ID up to10 times. Recover submitted attempts read-only on transport failure.
Own wrappers fix ONLY this slice's prefix/IDs/evidence and pin inputs. Shared
launcher/environment/infrastructure are unchanged. Failed-source SHA guard
and wrapper hashes are recorded. Keep every evidence input committed and every
file ≤20MiB. Do not rebuild imports or run an unchanged full regression.

Both source-binding.py --check and audit.py passed after all current modules became green.
Audit.py hard-checks receipts, immutable sources, caps, swaps, hashes and accepted
summary axioms. All #print axioms results are SUMMARY-BASED (ax1-prime), accepted
subsets only of propext/Classical.choice/Quot.sound. Raw NEP importAll/private/
hard-unresolved audit has NOT run; never claim coherence from successful imports.
No package-wide/frozen endpoint manifest replay has run. Final Audit is only
one scoped import/summary-axioms check of the new modules.

## Failures, with changed-source repairs

91200: ambiguous lift, constructor type inference and branch proof indentation.
91202: missing selected dictionary link at concrete constructor call.
91204: non-progress dsimp in an already symbolic V183 branch.
91213: missing parentheses around theorem RHS do blocks.
91217: multiplication bound needed Nat.mul_add, map composition needed rfl.
91218: multiline exact indentation. All six corrected before next compile;
failed sorryAx summaries earn no credit. No cap rise, timeout or memory kill.
Own stage ordering assertion fixed before launch (load allocator additions before
checking accepted consumer preparations); no compiler ID was consumed by it.
