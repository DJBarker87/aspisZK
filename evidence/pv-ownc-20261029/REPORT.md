# D429 ownership continuation — final report

**V229 SUSPENDED; V230 SUSPENDED; V239 SUSPENDED; V178 cleanup half SUSPENDED. No row restored, no checked witness-dependent native FINDING, no endpoint premise removed. Privacy target not yet established.**

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-own`; branch `codex/pv-ownc-20261029`; base/candidate `55358c233b`. New modules use PV_OWNC_. Exactly **100/100 Lean starts, 2/40 capped native scopes, 0 Kani**, using only62800–62899 and reserved audits62897–62899. [COMMITS.txt](COMMITS.txt) records the path-limited history through evidence preparation; the final report commit follows.

## What changed under own-1

Own-1 (D429) is applied directly. The obligation is structural binding of deployed1.94.1 source statements. Source-to-machine-code preservation remains **V370 at D381/D386**, named and retained; machine-code/LLVM correspondence was not pursued. Compiler-selected Link layout evidence remains reclassification within existing tool trust. No universal ABI/machine-code proof is introduced as an additional row blocker.

The26 new development modules prove53 local/model theorems: non-ZST source read bounds and pointer advance; source try_fold read→advance→filter/write order; equal-layout specialization and no shrink; explicit cap/buf/ptr/end stores before tail destruction; guard owner/current-generation transfer; unchanged represented byte intervals across handoff; POD prefix cleanup using original allocation layout; detached source no-free; direct abort without unwind; symbolic loop/identity preservation; two-step return ownership; initialized-prefix Vec publication; two conditional endpoint stores; padding-aware growth; byte/owner/frame-preserving push and inductive append; all72 pushes fitting cap254 from len64; FlatMap producer/consumer array order and272-cell destination initialization.

`PV_OWNC_InPlaceResult.guarded` composes the modeled filtering loop and two owner moves. `CursorVector.initialized` projects the returned prefix into the padding-aware typed Vec carrier. `FocusedReplay.returned` composes them using the exact three-path-kind predicate. These theorems retain their stated incoming represented-memory/ownership and empty-slot premises. They do not construct the actual source Vec instance or prove the complete callback. `LinkPush.forest` and `FlatMap.initialized` similarly retain their incoming typed-buffer instances. Neither a theorem name nor these conditional interfaces is whole-row credit.

[source-binding.json](source-binding.json) checks seven current deployed source hashes against ownb and records six exact source spans, ordered statements, named checked local laws and explicit abstraction differences. This is a **partial source coverage preflight**, not a complete structural (K-1 substitute) gate. [deployed-tail-sources.json](deployed-tail-sources.json) pins seven additional deployed source files, including push_mut, TrustedLen extension, SetLenOnDrop, dedup guards and unstable-sort internals. Capture is not proof. [resource-source-manifest.json](resource-source-manifest.json) inventories the31-module RDB2D consumed-law cone; it was not compiled or consumed here.

## Whole-row dispositions

**V229 — SUSPENDED.** See [V229.md](V229.md). Remaining source-level obligations are the initial schedule's actual full-Link byte/owner instance; actual Vec/IntoIter/guard constructor and complete Result/world binding; full endpoint translation loop; reserve/realloc-to-byte-owner transport and actual push instance; FlatMap allocation/SetLenOnDrop/source destruction; every sort/dedup move, initialized-length and POD suffix-drop stage; and composition with **PV_RDB2D_CollectorProgram.complete and its original value law**. Local stores/loops and resource logical-cell equalities do not supply that composition. This is the first incomplete row, so later rows were not advanced ahead of it.

**V230 — SUSPENDED.** V229's whole source instance, plus deployed usize/u16 shift, OR, stack-array stores and selected-op134 carrier association. Own-1 permits the structural route, but that source instance was not proved here.

**V239 — SUSPENDED.** Actual sparse Vec allocation/initialized-prefix/ownership instance and cleanup, raw ordered QM31 operation/builder association, monadic builder cardinality, sparse/dense transport and consuming public-point/length binding. Generic prefix-push laws are reusable model progress, not an instantiated sparse consumer.

**V178 cleanup half — SUSPENDED.** Actual owned-name/move/Path::join cleanup source binding into this shared byte/ownership world, including partial-buffer error cleanup and direct default-abort behavior, remains uncomposed. Inherited RDEAC physical/source qualifications remain. Diagnostic provenance belongs to **pv-diag2** and was not worked on or made this task's blocker.

Before: ownb's filtering byte/value model and local endpoint stores, with incomplete source/guard and whole-callback association. After: checked source-stage/guard/push/initialization models and partial source coverage, with the explicit whole-row joins above still open. Endpoint premises **removed/added/changed =0/0/0**. No witness domain, observer, simulator, dictionary or failure event changed. No same-public admitted witness pair showing differing allocation/destructor occurrence, order or size was established.

## Native validation and trust

Both optimized scopes use rustc**1.94.1**, deployed dependency versions and resolved feature union, release opt3, assertions/overflow checks off, panic unwind. Native01 checks4802 endpoint/lifecycle cases. Native02 changes the comparison to **full Link equality, including all21 kind variants**, and passes4802 lifecycle cases: normal outputs, pointer/capacity reuse, exactly one backing-store free, and controlled predicate-panic unwind at each tested position. Its exact metadata, command, feature lists, profile and MIR SHA are in [native-02/native-result.json](native-02/native-result.json). These are finite validation, not exhaustive source refinement. Injected predicate panics are controls, not a witness-dependent finding about the shipped predicate. Inherited suites were not rerun unchanged.

Every step resting on Rust/compiler/Aeneas/Charon semantic agreement is **reclassification within existing tool trust**, not premise removal. No new extraction or Kani gate was run or credited. rdea-1 retains allocator/runtime primitive outcomes, freshness/alignment/disjointness, realloc prefix preservation, actual deallocation and default failure handlers. Source stores, owner transfer and concrete continuation binding are not silently moved there. T remains exactly **entropy_law, entropy_kernel, observation**. E1/E2, real RunJoin, proof-account routing and L1/L2/L3 remain obligations.

## Final verification

[combined-audit.json](combined-audit.json) and numbered raw receipts retain exact target/command, exit, wall, peak RSS, swap, source revision/blob/SHA, dependency fingerprints and axioms output. **91 Lean starts pass;9 fail.** All failed/recovery outputs, including sorryAx, receive no credit. Every rejected proof was changed before retry; no cap increase, memory kill or timeout occurred.

| ID | Exact module | Exit | Wall | Peak RSS KiB | Swap |
|---|---|---:|---|---:|---:|
|62897|R1Z/PV_OWNC_StatementsAudit|0|0:00.29|481408|0|
|62898|R1Z/PV_OWNC_AxiomsAudit|0|0:00.19|480740|0|
|62899|R1Z/PV_OWNC_FocusedReplay|0|0:00.27|487676|0|

All three audit targets use source revision **dfc48ff5b31dc81bcc45b70babc43f7a982f2261**. Statement audit checks all53 new development theorem statements and prints five complete roots. Axioms audit checks all53 named results; only subsets of **propext, Classical.choice, Quot.sound** occur. The final focused replay's new composition has the same allowed axioms. This is one frozen new-model closure replay, not a privacy-endpoint/release replay. Maximum Lean RSS**519888KiB**; native peak**540348KiB**; all swaps0.

All actual scopes use MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000, one own scope at a time. All5673 external objects were verified against the coherent authority before the first compile and again before audits. [final-fingerprint.json](final-fingerprint.json) checks91 private project objects, tracked sources and every direct/transitive project import edge. No other job's project object was reused; no library/shared source/object was rebuilt or overwritten. Private objects and Cargo cache are **retained** for a subsequent pinned continuation; no rebuildable-cache deletion forces another dependency replay. No binaries or objects are committed.

## Process receipts and limits

The full host receipt-tree/shared-sent scan preceded62800 and found no62800–62899 collision; the final scan also finds none. Ownb's private objects had been deleted. This continuation rebuilt the needed inherited dependencies privately. The original69-entry dependency schedule was stopped after62853 completed; only the local scheduling parent was stopped/terminated, never a compiler or scope. The remaining unused schedule was replaced by a focused source-step route. Numbered receipts are authoritative.

62859's same-shell launch admission refused before any scope/Lean started. The task wrapper then tried to parse absent barrier JSON. Raw refusal files survive under `lean-62859/refusal-1/`; the own wrapper was corrected to recognize that reporting path and to search archived refusals for cooldowns. Retry retained the same unlaunched ID under ruling(m'). Every actual launch has allowed:true/exit0 and the mechanically verified minimum post-refusal cooldown is**181.320462seconds**. No refused proof or admission/cooldown violation was credited. No shared launcher/reservation infrastructure was changed.

The external-verification helper retains its inherited wording “before any resume compile”; its final timestamp is the pre-audit verification, not an assertion of a second initial check. [unsubmitted](unsubmitted/) retains two drafts receiving no credit; the final replay separately checks its own composition source. No wallet/account key was created, deleted or modified. No crates/programs, protected soundness file, observer, simulator or dictionary changed; no XR import, new axiom, sorry/admit/native_decide/implemented_by or raised limits. No committed file exceeds20MB. No push or merge occurred.

Stopped at **100/100 Lean attempts**. **Next deliverable:** build the actual initial schedule/Vec/IntoIter/guard source instance, bind the remaining source stores and all Result/world cleanup stages, then consume the RDB2D resource/value theorem. V229 cannot be restored from the partial source coverage or the new model laws alone.
