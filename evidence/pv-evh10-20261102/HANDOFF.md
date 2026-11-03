# D572 session2 context checkpoint — complete entropy return footprint

Continue ONLY /Users/dominic/ZK/.worktrees/pv-evh,
branch codex/pv-evh-20261029. Session2 started at a5e973e378 after a model-service
stall. Recovery commit83e5c75070 verified and committed the stopped session's
nine uncommitted accepted receipts90228–90236 BEFORE new proof work.
Read RESUME-D572.md and return-integration-session2.json for exact scope.
Target NOT established; endpoint/deployment rows removed NONE; T unchanged.
This is a context checkpoint, not budget exhaustion, a persistent host blocker,
or a checked counterexample against shipped source.

## Exact restart and resource state

**65/100 attempts consumed:45 accepted/20 failed.35 REMAIN; NEXT90248.**
79565–79581 consumed17;90200–90247 consumed48. Session2 consumed11:
90237–90247,7 accepted/4 failed. Recovery additionally collected9 earlier
accepted attempts90228–90236; they were already spent, not new session2 runs.
Cumulative148 receipts:100 accepted/48 failed.79582–79596 are unavailable after
17 inherited attempts.79597–79599/90297–90299 audits untouched; historical
79397–79399 untouched. Reserve audit budget. No WIP Lean proof, unresolved
submitted compile, missing receipt, or owned live scope remains.

Final read-only audit.py PASS: exact source revisions/blobs, dependency pins,
source/object/log hashes, caps, exits, walls, peak RSS, swap and all theorem
axiom prints. host-final.json reports zero pv-evh scopes. source-checks-session2
records all five caller/return/frame/entry checks. New peak4,469,580KiB, swap0;
new slowest3.58s. Historical peak4,616,200KiB remains. No cap rise, kill, timeout,
transport failure, native/Kani/extractor/full manifest/release replay.

90240 had TWO uncharged quiet-window refusals. The full180s cooldown was
observed before each subsequent HOST admission; three too-early local wrapper
calls were rejected before submission, documented in cooldown-local-guards-
session2.json. Third HOST admission was allowed:true and exit0, then90240
compiled ONCE. Both refusal-history files are committed. Quiet window was
released early; do not wait on its old until23:16:24 value without inspecting
the CURRENT marker/admission. No bypass or marker edit occurred.

Commit NEW source first; use ONLY:

    python3 tools/pv-evh10-20261102/stage.py PV_EVH_NewModule
    python3 tools/pv-evh10-20261102/compile.py 90248 PV_EVH_NewModule

Reuse pinned workspace /home/dombarker/project-offloads/codex-pv-evh-20261029
and runjoin32 cohort. Same-shell admission exit0 AND allowed:true; ONE6G/8G/
swap0/tasks64 scope, Lean-M7000. For refusals inspect exact last refusal epoch,
wait at least180s, SAME unlaunched ID, up to10 retries. Never reuse a submitted
ID. Preserve transport-recovery rules. No infra/library/LEAN_PATH/J.json/cap
changes. Accepted sources immutable: new consumers ONLY; never restage accepted
modules. Check EVERY new module name before writing. stage verifies every
accepted source/object pin. git add --sparse for evidence. Every evidence file
must remain at most20MiB uncompressed.

## Newly checked laws, with limits

90238 EntropyCallerLayout: at the identified adopted retry_attempt call, call
push8 + six saved registers48 + callee reservation232 gives caller_rsp=sp+288.
Mask input=sp+304, result=sp+352. Derives CallerSeparate rather than accepting
it independently;97-byte initialized result fits caller264-byte reservation.
Valid writable aligned nonwrapping memory remains runtime FRAME-ENTRY, actual
invocation/register/source interpretation V370. No full Result ABI size or
padding inferred. caller-source-binding-session2.json ties the exact call/GOT
relocation to adopted da36d6aa and existing source entry binding.

90240 StackStores: generic captured-register store footprints and ordered
composition. Memory ONLY; no native event silence or ownership inference.
90242 EntropyReturnFootprint:13 stores in EXACT adopted order, including all
96 staging bytes, interleaved96 returned bytes and Ok tag. Explicit register
sources are original64 and actual caller mask input. Symbolic byte laws,
inner128/mask preservation and external-write footprint, no concrete recurrence
normalization. Generator return_footprint.py --check PASS and permanently emits
named selected-store/outside lemmas. Accepted source is now immutable.
return_move_binding.py matches EVERY generator source/destination/extent to
adopted registers/stores, checks generated Lean bytes and pins hashes. It binds
the actual source's successful Self construction; it does NOT install a full
native world or prove compiler preservation.

90243 EntropyReturnComplete: all96 payload bytes/tag survive original64-only
cleanup; all96 staging bytes remain; moved-from inner64 remain; original64
is cleared. This utility's finish is a PHYSICAL MEMORY helper, not invocation-
key provenance. Use90247's anchored completed for actual source ghost keys.
90245 EntropyReturnSpatial: external old live bytes and heap coherence survive
under explicit exclusion of callee reservation AND initialized return footprint.
Mask input can remain live in caller memory. Runtime/heap fidelity NOT inferred.

90246 StackTransfer: ghost ownership transfer, same frame as existing relocation,
no additional physical stores, no destructor/zeroization. Not an actual
primitive/event-silence theorem.90247 EntropyReturnDelivery combines EXACT13
physical stores, both logical field transfers, ORIGINAL admitted owner/key
from ENTRY, and original64 cleanup. Derives original lookup after transfers
from initializer/fill/copy state; original_drop selects checked drop64 and
retains its emitted zeroize events. Both returned entropy fields come from the
SAME delivered original64; mask bytes equal ENTRY memory (outside_ready proves
initializer/fill/copy preservation). No per-lane/helper answer is supplied.
No64-step kernel normalization: preservation/outside lemmas are symbolic.

These are source-shaped physical/ghost laws for the reached successful branch,
NOT a complete successful actual entropy/proof/account execution. Source fill-
completion and nonzero-success guards, source mask/physical-memory association,
actual move/load/store/register/spill observation installation and advancing
native family remain OPEN. No discarded source failure or implicit success
assumption has been introduced.

## Exact retained FRAME/kernel obligations and continuation

FRAME-CALL, RAW-ABI, MOVE-COMPILER remain V370 compiler-cohort P.
FRAME-ENTRY (actual call memory), HEAP-ENTRY (actual allocator/coherent physical
memory), full KERNEL-WRITE (same-memory answer and outside-suffix preservation
on EVERY prefix/outcome), MOVE-L3 (all registers/spills/inner/staging residue
observations) remain runtime P. KernelFrame is weaker than KERNEL-WRITE;
syscall register REQUEST selection never proves what the kernel writes.
These are NEVER T fields or entropy_kernel joint density.

Next concrete deliverable: replace the actual entropy iteration's still-open
success continuation with the checked copy/read/decision/complete-return/
original-key cleanup substeps; retain all native read/store/register/spill
observations and guarded source results. Bind mask ENTRY bytes to the actual
source input under FRAME-CALL. Use EntropyReturnDelivery.completed/original_drop,
not the unanchored memory utility, for lifetime-sensitive consumers. Thread
rejected-iteration cleanup/retry states and source error/fault/exhaustion prefixes
into an advancing native family. Do NOT define execution from a supplied
whole-helper Result or claim the physical model alone supplies that family.

Then actual allocator metadata/padding/RawVec/Global/System ValidAnswer and owned
Vec/Heap/Box, full libc/TLS/io::Error/EBADF/hook/backtrace diagnostics, seven
callback installations and full entry. Resource failure stays WORLD; witness-
independent allocation/thread/TLS failure occurrence/timing stays V400-class P.
Arbitrary panic-hook SOURCE failures retain source projections.

ONLY THEN unchanged actual-family oraclePrefix/countTrace/nonce-store fileTrace
with D520/U/D524; ONLY THEN(v-prime) non-emptiness of successful ACTUAL worldRun
at opsNative AND allocator world. NativeObstruction62/op132 remain. No unrelated
MODEL witness, empty-domain shortcut, new T item, or endpoint weakening.

All V221/V222 deployedzeroize1.9.0/L3,V370/V371,rdea-1/V400,D159/D166 and all
L1/L2/L3/client/endpoint/deployment conditions retained. No push, delegation,
frozen Rust/program/soundness edits, key/account/funds action, deletion/refund.

## Failed attempts and axioms

90237 nested caller definition left folded: changed to targeted simp-only.
90239 Covers Prop was opaque to Decidable search: exposed arithmetic condition
in store's if.90241 selected store's own address and external hypothesis remained
folded: generator now normalizes all13 named descriptors and arithmetic bounds.
90244 finish remained folded at rewrite: explicitly unfold this small wrapper.
Each changed before retry; failed summaries including sorryAx have NO credit.
Local JSON check compared tuples with decoded arrays: normalized register/source
records to lists, rechecked successfully; no compiler/attempt consumed by that.

ALL #print axioms are SUMMARY-BASED (ax1-prime), accepted subsets only of
propext/Classical.choice/Quot.sound. summary-session2.json has exact per-run
receipts. axioms-classification-session2.json preserves inherited NEP_Driver
source pin, but NO full-data NEP walk/coherence claim. Raw release audit must
importAll/private and HARD ERROR on every unresolved constant. Never use NDR/
codex-cx-reconcile-cache. Hash/path agreement and passing imports are not coherence.
commits-session2.txt lists staged commits; final checkpoint commit follows it.
