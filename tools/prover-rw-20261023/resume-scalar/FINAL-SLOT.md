# Reviewable last-slot target (NOT RUN; lead allocation required)

Exact harness: `checks::paired_coordinate_native_resume` in `proof/lib.rs`.
After independent review and a fresh resource admission, the proposed target
command, in a fresh lead-allocated packet directory, is:

```
/usr/bin/timeout 240 /home/dombarker/.cargo/bin/cargo kani --manifest-path /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-scalar/proof/Cargo.toml --lib --exact --harness checks::paired_coordinate_native_resume --solver kissat --output-format terse -j 1 -Z unstable-options -Z stubbing --extra-pointer-checks --cbmc-args --unwinding-assertions
```

This is a command proposal, not permission, a runnable launcher, a compiled
harness, or evidence. ZERO Kani was invoked in this step. Do not resume the
admission-denied Rust compile in this step. No larger timeout/cap is proposed.
Lead must pin the final source/package/dependency/compiler/sysroot set and
review both the harness and missing native semantic producer before allocating
the last slot. Current native sources on the host have never been compiled;
local final proof/harness/prepare-script revisions must be synchronized with
fresh hashes before any future authorized job.

## Quantified graph and source cost retained

One unconstrained nonce32 + one unconstrained postbuffer64 + entry from all16
valid entries + primitive Ok/Err + i32 repr constrained ONLY to NonZeroI32 +
one raw_j:u8 whose remainder32 is the sole coordinate. A separate arbitrary
u64 ledger-before/after is bookkeeping only. Both selected modules see identical
source inputs and primitive result; no fixed callback dictionary/freshness law.

Each execution calls real Request::draw, literal fill under the sole stub,
real Draw::resume, all original32-byte zero scans and half copies, and actual
Zeroizing/array/iterator/scalar volatile/fence cleanup. Err does64 cleanup;
Ok rejection does leaf32/field32/64; success does64 while returning LIVE32 fields,
then the harness distinctly disposes field32/leaf32. The original module uses
unchanged zeroize with only its Cargo package name changed. Final projection
compares exact variant/error/retry and selected nonce/field/leaf bytes; all
input arrays remain complete and arbitrary. No result equality premise exists.

059 payload log:3 events *2 snapshots *64 bytes =384 payload bytes.
Scalar payload log:3 events *2 observations *2 bytes =12 payload bytes.
Lengths are fixed scalar fields. Byte storage is32x smaller, excluding layout
padding (no physical layout or solver-memory assertion). On any Ok path the
observers read2*(64+32+32)=256 source bytes in059 versus2*(2+1+1)=8 now;
Err128 versus4. The32 observer's extra high scalar is constant0.
Observer loops:059 loops up toN at each pre/post; scalar observer has0 loops.
Current events() returns a fixed three-event tuple, no full-array snapshots.
Pairing doubles actual source scans/copies/wipes relative to a single-source
check; this packet promises neither a smaller whole solver formula nor faster
runtime without measurement. The size reduction established is the observation
subgraph, not a native cost bound or successful final proof.

## Native relation blockers, not additional premises

Source-place role map, source-step projection argument and finite arithmetic
lemmas are review material. They do not implement a full Rust operational
semantics/refinement. The new MIR compile was admission-denied. Old054 supplies
rejection bindings only; its recorded successful branch has an empty statements
list and supplies no success field-move witness. No new native/compiler check,
Kani success, OS-world transport, controller reachability/finite16 or complete
privacy/adoption result follows. E1 and all L1/L2/L3/native/controller/client/
artifact/performance obligations remain unchanged. Both deployed targets not yet
established.
