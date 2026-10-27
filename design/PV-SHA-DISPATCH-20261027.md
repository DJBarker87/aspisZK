# SHA dispatcher decision packet

Decision packet for the pinned sha2 0.10.9 / cpufeatures 0.2.17
prover. No build has been changed. Target not yet established.

## Executed backend and artifact association

The recorded extraction build has sha2 features `default,std` on x86_64 Linux;
`force-soft`, `force-soft-compact`, and `asm` are absent. `sha256.rs` therefore
selects `x86::compress`. Its `shani_cpuid::get()` checks SHA, SSE2, SSSE3 and
SSE4.1. True selects the SHA-NI implementation; false selects Rust `soft`.
Both are compiled. Source and fingerprints are pinned in
`evidence/pv-cblib-20261027/SHA-BACKEND.md` and its linked inventories.
The deployed executable/CPU association must be distinguished from this
source/build selection. The measured host is the recorded Intel Core Ultra 7 155H. The isolated
release build records empty rustflags and sha2 features default/std;
runtime checks report sha/sse2/ssse3/sse4.1 all true. On this build and host,
`x86::compress` therefore executes SHA-NI via runtime detection, not soft.
With all four target features statically enabled, cpufeatures instead
returns true without CPUID; the recorded empty rustflags do not take that
shortcut. A CPU lacking one of the required features takes soft.

The repository does not supply a uniquely associated deployed native prover
binary/CPU in this worktree. V372 platform pins remain P in research revision
624e93d86c240ef1ed0560b916e4c7a4a0ce8a1b. The extraction fingerprint is not a
release artifact. Thus the exact deployment conclusion is conditional on
those recorded build/CPU pins; an arbitrary deployed CPU cannot honestly be
assigned a unique executed branch. No deployment association is fabricated.

## Option A: D187 prover-only soft build

The exact Cargo feature at this pin is **`sha2/force-soft`**, not a guessed
`sha2_force_soft` Rust cfg. The `force-soft-compact` feature has higher
precedence and selects a different implementation. Default/std can remain
on. A future change must be confined to the host-prover dependency graph and
its invocation; workspace-wide feature unification can propagate features.

An invocation-only proposal is:
`cargo build --release -p aspis-r1-cost-probe --features ct-host-prover,sha2/force-soft`
with the actual deployed prover binary target added to that invocation. No
Cargo.toml edit or global RUSTFLAGS is necessary. The package/target must be
chosen from the eventual deployed prover manifest, which is still a pin gate.
Separate verifier/SBF invocations omit that feature; Cargo feature activation
is per invocation. Their commands/dependency graph are unchanged, and the
verifier's concrete digest uses its syscall backend. SBF isolation must
be confirmed from its dependency/feature graph and all three rebuilt ELF
pins before adoption; this packet performs no build change or full timing
gate. Soft source proof does not establish loan, buffer, padding or deployed
association obligations by itself.

## Option B: prove SHA-NI instruction semantics

Model `_mm_sha256rnds2_epu32`, `_mm_sha256msg1_epu32`,
`_mm_sha256msg2_epu32`, plus SIMD add/shuffle/align/blend/load/store,
endianness, pointer bounds and CPUID dispatch. Prove the x86 instruction
semantics implements the scalar recurrence and compose the concrete
machine-code/source/compiler relation. Treating intrinsic semantics or
CPUID behavior as assumed native facts has an explicit trust cost.

The owner's T is capped at `entropy_law`, `entropy_kernel`, `observation`.
No fourth field or folded native premise is permitted. Thus an assumed
intrinsic model is not an acceptable closure under the current contract;
these facts remain P obligations. The explicit cost is a proof of the SHA/SIMD
ISA model, memory/alias/alignment behavior, compiler intrinsic lowering,
CPUID decision and CPU compliance; trusting any of them without proof would
expand or hide T, which the owner forbids. The existing latency item V371
does not prove instruction functional correctness.

## Option C: retain dispatcher and prove both branches

Prove scalar compression, SHA-NI compression and feature detection, then
join the branches at `x86::compress`. This preserves current runtime behavior
but carries both proof closures. An alternative independently verified
prover SHA implementation would itself be a D187 rewrite requiring source
refinement, release-artifact and timing adoption gates.

## Measurements and recommendation

`dispatch-census.json` records **3,149,033 callbacks** in one successful
`prove_masked_fixture` S2 transfer call, deterministic seed [37;32], output
57,607 bytes. Setup, verifier calls and retry attempts are excluded. The
production steady-attempt inference is 3,149,030 passed callbacks (subtract
three fixture-secret hashes), plus one direct durable-ledger reservation SHA:
**3,149,031 SHA calls per such attempt**. This is a source-based correction of
a fixture census, not a census of every deployed run or a bound on retries.

Both experiment binaries use sha2 0.10.9, cpufeatures 0.2.17 and an optimized
release profile, with the same sources/toolchain and empty rustflags. Soft
adds only `sha2/force-soft`. The 29 observed input-part shapes are benchmarked
with seven samples each, preserving each update's segmentation. All compared
digests agree. `dispatch-build-fingerprints.json`, the five `dispatch-*`
run directories, and `dispatch-projection.json` retain exact commands,
features, hashes, exit, wall/RSS/swap, source revision and N/A axiom receipts.
No deployed build was changed and no full timing gate ran.

| Quantity | Measured / projected value |
|---|---:|
| Census-weighted native SHA time | 0.85749 s |
| Census-weighted soft SHA time | 6.78362 s |
| Weighted soft/native per-call ratio | **7.9110×** |
| Projected added prove time | **5.92613 s** |
| 13.63 s historical baseline → soft estimate | 19.55613 s, +43.48% |
| 13.98 s historical baseline → soft estimate | 19.90613 s, +42.39% |

The small three-hash/ledger correction is below the precision of this
projection and is not separately microbenchmarked. Historical D172 medians
come from `design/PROVER-RW-20261023.md`; they are not interleaved controls
for this shared-host experiment. Counts and per-call medians are measurements;
the summed delta and end-to-end numbers are estimates. They exceed both the
15 s and +10% gates by a substantial margin, but constitute no actual gate
failure or formal cost theorem. Shared-host contention and frequency changes
remain measurement limitations; raw samples are retained. Weighting the best recorded soft sample against the
worst native sample gives a +3.55 s sensitivity estimate; the opposite
extrema give +12.09 s. These are not confidence bounds, but even the
optimistic combination exceeds the historical headroom.

**Recommendation:** keep the current SHA-NI build. Complete scalar block and
digest semantics as the reference, then prove the SHA-NI instruction/dispatch
refinement and the concrete compiler/artifact association. Under the capped T,
assuming intrinsic correctness is not an admissible shortcut. Do not adopt
a force-soft D187 rewrite on these measurements; a later substantially faster
verified soft implementation would require its own equivalence and adoption
gates. The projection does not authorize changing or relaxing either gate.
