# D435: V229/V230 own-2 qualification rejected

**V229 SUSPENDED under own-1. V230 SUSPENDED under own-1. No RESTORED row,
no witness-dependent FINDING, no endpoint premise removed.** The complete-cone
no-external-read condition fails at the shared mandatory initial allocation.
Privacy target not yet established.

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-own`; branch
`codex/pv-owne-20261029`; base/candidate `325ba5f047`. The prompt chain,
pv-common with all current lead rulings (including own-2), repository rules,
and prior reports were read. No existing proof or own-1 evidence was edited.

## Exact reason the rows cannot be restored by own-2

Both no-argument functions reach the legacy builder's unconditional
`Vec::with_capacity(127)` before schedule processing. The deployed1.94.1
allocator path is RawVec → Global → __rust_alloc → __rdl_alloc → System →
libc::malloc. The host's pinned glibc2.39 normal allocator path reads a mutable
global byte at ELF address0x20b188 (`__libc_malloc+0x14`, instruction0xad764),
and reads thread-local allocator state at instruction0xad79a
(`mov %fs:0x0(%r13),%rdx`). A retained instruction writing the global byte and
the writable .bss section range independently confirm mutability.

[STATIC-CHECK.md](STATIC-CHECK.md) records the source path, all requested
application/iterator/flat_map/collect/sort/dedup categories, allocator entry
points and failure branch, hashes, and the limits of the negative check.
[static-capture.json](static-capture.json) retains44 byte-pinned sources,
application git blobs, rustc-Vv, the inherited per-unit deployed feature graph
and lockfile, allocator disassembly and binary/runtime hashes. All six captured
application/configuration files match this branch byte-for-byte.

The mandatory path is a counterexample to the complete-cone *qualification
condition*. This is not a proof that allocation sizes/order or output values
depend on the witness. No same-public witness pair with distinct observations
was exhibited. No D159 privacy leak is claimed.

rdea-1 still covers primitive allocation outcomes and failure/abort handlers.
Own-2(c) expressly retains allocation failure there. It does not explicitly
exempt **successful allocator TLS reads** from own-2's no-external-read test,
and the user's instruction requires stopping a row on *any* external read.
No additional exemption, observer quotient or trust item was invented.

Consequently, the evidence class **“exhaustive over a singleton input domain,
deployed compiled artifact” is NOT assigned**. The current result is static
qualification rejection with supporting runtime inspection. It is neither
finite validation of a universal claim nor a source-binding proof.

## Requested conditional work and retained proof assets

| Item | Disposition |
|---|---|
| V229/op133 literal Result proof | Conditional on qualification; not started. Existing PV_RDB2D op133 literal/value cone remains unchanged. |
| V230/op134 literal Result proof | Conditional on qualification; not started. Existing MasksLoop/MaskChunk/MasksValue laws remain unchanged. |
| One deployed release execution per root | Not run, per explicit stop-on-external-read instruction. |
| Byte comparison and crate fingerprint cross-check | Not run; no new value bytes or value/fingerprint hashes claimed. |
| Allocation/abort | Mandatory first request and actual allocator entry points checked; inherited1016/alignment2 request/null-abort observation retained as supporting finite validation. No new allocation trace or abort execution. |
| Own-1 continuation | Stopped at the requested qualification obstruction; no new source binding is asserted. |
| V228 | No status change or restoration audit in this task. |

`PV_RDB2D_OrdinaryOriginal` was inspected: it concerns ordinary sampler
decoding and does not itself pin op133/op134. The separate op133 cone and
MasksValue do contain the relevant model literals/laws, but none is promoted
to a new deployed closure after failed qualification.

V229's exact current own-1 frontier remains the actual endpoint-counter
stack arrays/mutable stores/Result-world caller binding at legacy builder
line242 and counter lines246–263, followed by the unreached later collector
stages. See [prior V229 status](../pv-ownd-20261029/V229.md) and
[prior report](../pv-ownd-20261029/REPORT.md). The corrected inherited
FocusedReplay remains explicitly uncompiled; it was not consumed.
V230 retains V229's collector association and its deployed usize/u16 shift,
OR and stack-array carrier binding; see
[V230](../pv-rdb2d-20261028/V230.md). All previous own-1 byte/ownership,
resource-program and value evidence remains supporting evidence.

Before/after statuses are SUSPENDED→SUSPENDED for both rows. Endpoint premises
removed/added/changed=0/0/0. T remains exactly entropy_law, entropy_kernel,
observation. V370/D381/D386 remains the named own-1 compiler-preservation
boundary; no machine-code correspondence obligation was added. No simulator,
dictionary, observer, witness domain or failure event was changed.

## Validation and process

The committed rejection checker `tools/pv-owne-20261029/static-check.py`
exited0 at source revision `495f3685e3`; the capture records the full revision.
It checks branch/worktree identity, every captured source hash, six tracked
application blobs, the retained client SHA256, actual allocator-shim target,
malloc TLS/global-read instructions, a write to the same global byte and
the writable ELF section. This is a read-only source/ELF inspection command,
not a compiler, proof replay, or execution of either requested Rust function.

**Lean0/60; capped native scopes0/30; Kani0.** No IDs were consumed, including
audit IDs63497–63499. No host build or compiler was launched; admission,
scope wall/RSS/swap and #print axioms are therefore N/A. There is no formal
release result, new theorem, combined Lean audit or manifest replay to report.
The budget was left unspent because the user explicitly ordered stopping
each row on an external read, not because of contention or a launcher fault.

The baseline client hash is
`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`;
host libc hash is
`3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf`.
Both were read, not run or modified. No binary/object is committed.

No crates/programs/protected soundness file changed; no wallet/account keys
created, removed or modified; no push, merge, XR import, new axiom, raised
limit, full checkout or file over20MB. Only this task's evidence and checker
paths changed. Stage commits are in [COMMITS.txt](COMMITS.txt); the final
report commit follows that list.

Next concrete proof deliverable remains the inherited own-1 source/world
instance. Applying own-2 instead would require a lead rule explicitly
defining a runtime boundary that permits this successful allocator-state
read; this report does not assume such a rule exists.
