# Claims candidate: common allocator request, failure and owner-drop control

S1/S6 remain OPEN. Candidate `891a213f79` remains NOT ADOPTED. This packet
checks the complete frozen/candidate functions against a COMMON explicit
allocator interface, covering both allocation outcomes. It does not establish
the concrete SDK allocator/runtime instance, initializedness, whole equivalence
or an enclosing SDK premise removal.

## Exact claim

Two Kani harnesses execute the complete Claims bodies:
`native_claims::proofs::allocation_failure` and
`native_claims::proofs::allocation_success`.

The original body is exact at adopted freeze
`25866ec331cc7ce27dd9956609c11d32fa8fa58a`. The isolated safe-storage body is
exact at `891a213f79`. Both real `heap::uninit` / `heap::filled` procedures,
Vec/Box conversions, error propagation and Box destruction execute. No source
function, input Prefix, WireError or QM31 carrier is simplified. Imports are
factored, two existing wire proof constructors are appended, and a cfg(kani)
wrapper exposes the original private function to the paired test. Whole-crate,
ABI and release-artifact identity are not inferred from this source factoring.

Four explicit cuts are present on each harness:

1. `ValidatedRecord::decode_k`: common normal-return tape, checking record25,
   same frame pointer/length, N29 and exact call offsets0/29/58 before returning
   arbitrary full native rows or any release WireError/payload.
2. `alloc::alloc::alloc`: common success/failure choice. Each call ASSERTS it
   is the sole request, size1392 and alignment4. Failure returns null. Success
   obtains fresh ZEROED storage from the separate real `alloc_zeroed` path,
   recording the pointer. That fresh-storage model is explicit, not an
   arbitrary prior heap or a native Bump allocator proof.
3. `alloc::alloc::dealloc`: records and checks the same allocated pointer,
   size1392, alignment4 and exactly one call; actual memory release is a no-op
   in this interface. The frozen SDK Bump dealloc empty-frame fact already
   exists separately (`sdk-release-allocator`); this new cut is not called a
   proof of concrete dispatch to that SDK implementation.
4. `alloc::alloc::realloc`: any reached call fails an assertion. Thus neither
   actual function's reachable conversion path reallocates on this domain.

The native returned Box is observed AFTER the complete function call: its
pointer must equal the allocation result, its full Claims array is copied for
comparison, and the actual Box is dropped. Both functions' native typed Drop
paths execute, reaching the explicit deallocation interface. This observation
is not an owned/simplified replacement passed to either function. No native
allocator/deallocator memory effect or SBF ABI identity is claimed from it.

For a failed common allocation, BOTH functions return the actual native
`Error::Allocation`, before any decoder call and with no deallocation call.
For success, both functions make identical checked decoder-call prefixes,
return equal full Rust errors or all348 returned u32 coordinate words, and
each owner is deallocated exactly once (including decoder rejection paths).
The returned Box pointer is the same pointer each execution allocated; the
two separately modeled fresh allocation pointers need not equal each other.
Mixed returned outcomes, extra/missing allocations/frees, changed layouts,
changed pointers or reallocations fail checks.

All87 QM31 cells' four raw u32 words, the decoder's first-error position0..2
or no error, and every WireError payload are symbolic. The complete Prefix
has zero root and27 record references to the same zero-filled frame, with
length0..3717; the decoder cut does not read its contents. No arbitrary-Prefix,
allocator state, decoder abort/effect or reached native SDK context is inferred.
No independently successful source child or input canonicality premise is
introduced.

## Validation and coverage

Both bool choices of the common allocation interface have been checked. Each
helper contains four cover sites: allocation failure, first decoder rejection,
third decoder rejection and success. The failure harness reaches1/4 sites;
the success harness reaches the complementary3/4. The other sites are
unreachable under each fixed allocation choice. This is not misreported as
all four sites reachable in either individual partition.

| Attempt | Target | Exit | Wall s | Peak RSS bytes | Sampled aggregate bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| v1 | failure compile | 0 | 0.724323 | 255623168 | 193478656 | 0 |
| v2 | failure: 0/1102 failed, 1/4 covers | 0 | 4.757697 | 409518080 | 428949504 | 0 |
| v3 | success compile | 0 | 0.674675 | 254951424 | 191692800 | 0 |
| v4 | success: 0/1102 failed, 3/4 covers | 0 | 28.776991 | 1146601472 | 1240891392 | 0 |

Official Kani0.67.0 aarch64-apple-darwin, archive SHA256
`7fd0b71130aa37bd1e346eba675aad09e9b66e4b383f707fc657330ceb29eeec`;
rustc `1.93.0-nightly (53732d5e0 2025-11-20)`. Each input pins package,
compiler, host sysroot, all88 core sources, full selected native source and
Cargo metadata before/after. Exact source revision, command, environment,
snapshots, status/timing/output hashes are retained. Rust is optimized with
overflow checks; unwind32 with unwinding assertions, DEFAULT Kani checks.
No `kani::assume`, transmute, custom axioms, native_decide or resource-option
overrides. `#print axioms`: N/A, no Lean theorem or axiom added.

Each job held the shared atomic local compiler lock and used the same sampled
aggregate2GiB RSS watchdog,64-process bound and180s timeout. No resource stop,
cap increase, SSH/NUC, cold build, Aeneas or full manifest replay. These focused
Mac watchdogs are not hard cgroups/MemorySwapMax enforcement; observed process
swaps are zero. They do not acquire build-host execution authority.

A source-only97-file kit reconstructs EVERY selected source hash in every
accepted input. First preparation v1 had a filename-replacement-order bug and
failed its post-generation input comparison before any compiler launch; its
preparer, binding and failure record are retained/excluded. Fresh v2 fixes only
the selected-root filename, and matches all contemporaneous hashes. No compiler
rerun or historical receipt rewrite was used to repair that preparation audit.
The origin inventory is a source audit, not a retroactive pre-run pin.

Read-only source-only focused-extractor-proof-packet-v1 check:

```
python3 tools/s1-claims-allocator-control-20261025/check.py
```

PASS70 source/evidence hashes, exact Git body bindings,97-file reconstruction,
all receipts, source/tool stability, explicit cuts, complementing case covers
and the excluded preparation failure. No binaries distributed. Production,
artifacts and other sessions' worktrees/tracks are unchanged.

## Retained obligations and source decision

This is OTHER: full-result/request/drop-control equivalence under explicit
common cuts. It is not native TOTAL/R22 for arbitrary allocator/SDK inputs.
Default outer overflow/bounds/unwinding checks pass on its exact domain;
opaque/changed child behavior and source/runtime transport are not discharged.

The previous `d05f5aa31d` check already compares the complete native results
under default actual host allocation helpers. The new result adds null-return
allocation rejection, exact request layouts, no-reallocation and owner-drop
request control. It does NOT turn either check into arbitrary allocation,
private-byte-frame, native effect or source-to-model equivalence. In particular:

- Success storage is zeroed, and deallocation is an explicit no-op cut. The
  source/native allocator state, prior-byte and lifetime/valid-owner transport
  still need a concrete interpretation, including target dispatch.
- The original initialization check remains failed at the union-pointer
  operation (`5c7b15d36b`). This packet has no uninit-checks and cannot repair
  it. Child abort/divergence, cleanup memory effects and complete reached-state
  provenance remain open.
- Candidate extraction/kernel proof, actual Claims/Terminal/Std/native source
  installation, caller/effect/oracle joins, cost/stack/two-transaction gates,
  adoption and source/artifact/affected-parent re-pins still apply. The prepared
  extraction release remains disabled pending fresh reviewed host admission.
- The shared S6 original/current/kernel/enclosing/release join remains
  lead-owned; S2 remains transferred. No competing integration is attempted.

No source adoption decision is taken or requested by this gate. The isolated
candidate becomes more reviewable, but cannot replace the frozen verifier
without the remaining gates. The <=2^-100 per-attempt target without grinding
credit and whole S1/S6 remain not yet established.
