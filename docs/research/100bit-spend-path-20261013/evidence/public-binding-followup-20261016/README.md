`verify.py` passes read/hash-only: 116 members, nine standard-only axiom reports.
The exact sources are committed at `162f2a4d0` (preceding helper source
`9d85f36e4`), on `ebe378259` rebased onto the accepted `99263bea0`.

| Exact focused target | Exit | Wall seconds | Peak RSS KiB | Swap |
| --- | ---: | ---: | ---: | ---: |
| ExtractedPreparationSerializerWhole | 0 | 9.221 | 3,884,812 | 0 |
| ExtractedPublicPreparationBinding | 0 | 2.212 | 3,849,708 | 0 |
| ExtractedFirstCallerReachability | 0 | 2.364 | 3,863,656 | 0 |

Each scope used MemoryHigh=6 GiB, MemoryMax=8 GiB and MemorySwapMax=0;
receipts record exact commands, sources, source revision/hash, import closure,
producing cache keys, runtime pins, time, RSS and every requested `#print axioms`.
All nine final reports contain only propext, Classical.choice and Quot.sound.
There was no dependency build or package replay.

The actual `public_transcript` success now supplies `PublicBinding`'s serializer
success `hs` for both variants. Every source-carrier field, the same bytes and
C1 root, and the returned transcript are retained.

The exact production first body is present in LLBC. The current r18 translator
fails on Observer arrow types; that failure is retained. Replaying the same
LLBC with the existing accepted static translator succeeds (exit 0, 0.4023 s,
63,712 KiB RSS, swap 0). Its tracked recipe pins the binary and the source
audit matches all 38 patched files plus the backend lock. No tool was rebuilt
or patched. The complete emitted first body is then bound to the checked
actual decoder/selector and explicit universal tx1, observer and error-map
parameters. The successful caller prefix supplies actual decoder success and
the exact public passed to that continuation. All four external globals are
eliminated from its axiom closure.

Downstream tx1-to-helper reachability, SDK/runtime preservation and custody
remain outside this caller-prefix theorem. The generalized SDK/downstream
error carriers and diagnostic stubs are explicit in `first-binder-audit.json`;
no theorem is accepted about stub behavior. Custody is separate from B's
metadata projection boundary.

The initial tactic parse error, generic error-carrier proof error, two guarded
preflight stops when an external Lean job arrived, and a launcher-only syntax
failure are retained. Neither preflight stop started a formal target. The
corrected runner checks immediately before actual Lean launch, after hashing,
and monitors external Lean by cgroup. No external process was signaled.

No SBF rebuild or runtime harness was run. A separate coherent refresh follows
for A's expanded current caller Types/Funs; these receipts retain the original
pinned preparation universe and are not silently mixed with the new objects.
