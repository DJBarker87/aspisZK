# D436 own-2' result

**V229 SUSPENDED under own-1. V230 SUSPENDED under own-1. No row restored,
no witness-dependent FINDING, no endpoint premise removed. Privacy target
not yet established.**

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-own`, existing sparse
checkout; branch `codex/pv-ownf-20261029`, base `95971605dd`. The prompt chain,
updated pv-common, repository security/proof rules, prior ownership reports,
and owne REPORT/STATIC-CHECK were read. Only ownf evidence/tools paths changed.

## Exact stop reason

The two old reads are now explicitly **ALLOCATOR-INTERNAL**, permitted by
own-2': malloc initialization byte `0x20b188` at instruction `0xad764` and
tcache TLS at `0xad79a`. The old literal own-2 rejection is not repeated.

Expanded inspection finds two different reads:

* **OTHER:** `malloc` at `0xad7b5` reads process-wide
  `__libc_single_threaded` (`0x20c040`). The pinned libc's `pthread_create`
  writes that same `.bss` byte at `0x9d336`, outside allocator entry points.
  The installed public header identifies it as process threading state.
  An empty tcache bin leads to this read before the ordinary successful
  arena-allocation path. Neither root requires a nonempty bin.
* **OTHER:** `free` at `0xade59` saves incoming general `errno` TLS and
  restores it at `0xadeae`. Its TLS-offset slot `0x203df8` is independently
  identified by `__errno_location` at `0x2a6e4`. This is shared per-thread
  error state, not allocator-owned tcache state.

The classification applies own-2' literally to the allocator's **own internal
state**. A datum does not become allocator-owned merely because malloc/free
reads it. These externally shared process/thread variables therefore do not
satisfy the confinement requirement. This is a qualification obstruction,
not a claim that either read changes the u16 result, and not a witness leak.

[STATIC-CHECK.md](STATIC-CHECK.md) gives the complete root-to-first-allocation
path, empty-cache reachability, instruction-level witnesses, classification,
and scope limits. The user requires stopping a row on **any OTHER read**;
the first witness already stops both rows. No broader exception for shared
threading state or preserved incoming errno is assumed.

## Requested proof/execution disposition

| Obligation | Result |
|---|---|
| Complete-cone qualification under own-2' | Rejected by explicit reachable OTHER read; not a positive purity certificate. |
| Address-independence proof | Not reached after required stop; no new relocation-invariance proof claimed. |
| Named literal Result laws for op133/op134 | Conditional work not started; existing op133 and MasksValue laws retained without promotion. |
| Deployed release execution once per function | Not run after required stop. |
| Literal byte comparison and crate fingerprint cross-check | Not run; no new value/fingerprint hashes claimed. |
| Allocation and abort under rdea-1 | Existing primitive outcome/failure-handler boundary retained; no new allocation trace or abort execution. |

The evidence class **“exhaustive over a singleton input domain, deployed
compiled artifact” is NOT assigned**. This is static/runtime inspection of a
negative qualification witness, not that evidence class, finite validation of
a universal native law, or a source-binding proof.

## Validation and retained obligations

The read-only checker passes, revalidating44 complete pinned source files and
all six application/configuration files against HEAD; it checks both old
allowed reads, both new OTHER reads, the external threading writer, errno TLS
identity, writable symbol, headers, runtime hashes and root call chain.
[static-capture.json](static-capture.json) retains full disassembly, symbols,
sections, headers, rustc1.94.1 identity, libc2.39 identity and the inherited
source-capture SHA256. [check-output.json](check-output.json) is the final
checker stdout. Initial check at `c1e853ac44` passed; the final check at
`f5ddc37902` passed after adding checker hash/branch/worktree metadata and
correcting the prime-character label. These are read-only inspections, not
unchanged formal/full-manifest regressions.

**Lean0/60, capped native scopes0/30, Kani0.** No Env-J IDs consumed, including
63597–63599. No compiler or requested root execution launched. Formal target,
formal wall/RSS/swap and `#print axioms` are N/A; no new Lean declaration or
formal release result exists. Inspection exit/wall/source revision and exact
checker SHA256 are in the capture. The checker source is committed here.
Budget is unspent because of the user's explicit OTHER-read stop condition,
not host contention, missing cache or launcher failure.

The retained client hash is
`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`;
libc hash is
`3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf`.
No binary/object is committed. The client's inherited deployment feature and
lock metadata remain in the SHA-pinned owne capture; no new artifact is built.

Before/after: V229 SUSPENDED→SUSPENDED; V230 SUSPENDED→SUSPENDED. Endpoint
premises removed/added/changed=0/0/0. T remains exactly entropy_law,
entropy_kernel, observation. V370/D381/D386 compiler preservation and rdea-1
remain named and retained. No simulator, observer, dictionary, witness domain,
failure event or implementation changed. No new tool-trust reclassification
or source-to-machine-code obligation is asserted.

The own-1 frontier remains V229's actual initial endpoint-count arrays,
mutable stores and Result/world caller binding at tree242/246–263; later
collector stages and V230's usize/u16/stack-array binding remain open.
All own-1 evidence is retained; the corrected inherited FocusedReplay is still
uncompiled and is not consumed. V228/V239/V178 statuses are unchanged.

The next concrete deliverable under the current rules is that own-1 source
instance. Own-2' cannot restore these rows without a rule additionally allowing
these two shared process/thread-state reads; this report does not supply or
assume that rule.

No crates/programs/protected soundness files, wallet/account keys, shared
host sources/objects or other worktree changed. No cap raised, binary or file
over20MB committed, push or merge. `git diff --check` passes. Path-limited stage
history is in COMMITS.txt; this final report commit follows that list.
