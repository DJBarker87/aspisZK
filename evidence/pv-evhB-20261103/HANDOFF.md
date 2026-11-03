# PV evhB allocator/callback context checkpoint

Continue ONLY `/Users/dominic/ZK/.worktrees/pv-evhB`, branch
`codex/pv-evhB-20261103`, base `034dfee6ac`. New sources use `PV_EVHB_`;
never edit/restage accepted PV_EVH or PV_EVHB sources. No push/delegation,
Rust/program/soundness edits, native run, Kani run or key/funds action occurred.
No endpoint/deployment row removed; T unchanged; target NOT established.

## Pending final checks (update after they finish)

Normal 91200–91220 consumed: 21 charged, 15 accepted, 6 rejected. 76/97 remain.
91221 PrivateSaltsNew has NOT launched: two uncharged reservation refusals.
Its source is committed and staged; never count these as Lean attempts.
A local queue is observing the latest full 180s cooldown and will retry the
SAME 91221 up to ten times, then stage/compile the NEW audit target at 91297.
Do not submit a second copy while that queue lives. Inspect actual receipts
and current host scopes before resuming; never resubmit a submitted ID.
Next normal ID is 91221 until a receipt exists, then 91222. Audit91298–91299
are untouched. Audit91297 is unused until submission/receipt appears.

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

Run source-binding.py --check and audit.py after all current modules are green.
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
