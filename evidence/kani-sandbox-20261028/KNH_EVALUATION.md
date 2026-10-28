# KNH isolated Kani evaluation

Status: preparation. Sandbox diagnostics only; no proof obligation receives credit.

Budget: 40 new-version Kani runs, 10 pinned-version controls, zero Lean.
Only KNH evidence and private host scratch are writable. No frozen code changes.
One admitted scope at a time: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. No timeout or memory-killed shape is rerun unchanged.

Stages: (1) isolated installation/pins; (2) return-shape and loop probes;
(3) K-1/K-2 fidelity and cross-version controls; (4) audit/recommendation.
Each stage is committed locally. Admission must be exit0 AND allowed:true.

Frozen release source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline/trust/security contract unchanged. No ELF rebuild trigger: this job
uses a dependency-free scratch crate, not deployed verifier source.

Stage 1 complete: isolated Kani 0.68.0 / CBMC 6.11.0 installed. Published bundle
SHA256 32e2b484d73ede0bbf64a2cf0879c4259422497d8aec4ee67d448de9ae7843d3.
KNH_INSTALL_FILES.json inventories installed regular files; KNH_INSTALL.json
records download URL and private Rust toolchain. KNH_CACHE_IMPORT.json records
copies from the read-only leaf cache into this lane's retained private cache.
No Lean objects are consumed by this zero-Lean job.

The probes use standalone Kani on one Rust scratch crate source per run. Cargo
never resolves or compiles dependencies for them; cfg-if/libc are unreachable.
The exact frozen release Cargo.lock is copied into scratch and checked before
and after every run. Each receipt records the empty external dependency graph
and frozen-lock hash. This is **not** a replay of the frozen workspace graph,
and gives no frozen-code or deployed-feature proof credit.

Stage 2 observations (in progress): N004 and N010 reject borrowed return stubs
for missing Arbitrary. N002/N005/N007/N008/N011 encounter a contract codegen
panic at opt-level=3 (undeclared contract closure). N013 checks the one-byte
Vec weak callee at opt-level=1, still optimized. No timeout was rerun.
The final packet will distinguish semantic failures, codegen failures and
CLI failures. N001 consumed a run on invalid standalone argument forwarding;
our runner was repaired to use RUSTFLAGS, whose opt-level is printed by verbose
Kani. Transport upload was compressed after the oversized command reset twice;
no verifier had been submitted. These are own-wrapper fixes, not changes to
shared host infrastructure.

Stage 2 complete (N001–N034). At opt-level=1, the for/enumerate pair
(N031) and dynamic borrowed-record while pair (N032) each produce the intended
positive PASS and negative assertion FAIL. The borrowed record contains an
arbitrary-length slice, length0..4; its invariant actually reads that record.
These are minimal loop diagnostics, not the original full NCP verifier leaves.

Return shapes: &[u8], Result<&[u8],u8>, Vec<u8>, Result<Vec<u8>,u8>
stub_verified codegen fails for missing Arbitrary (N004/N010/N016/N022).
Box<u8> has a complete narrow control packet: weak callee N025 PASS,
inverted N026 FAIL, real caller N027 PASS, unimplied assertion under verified
stub N028 FAIL, modifies violation N029 FAIL, real mutation N030 PASS.
Box slices and production error types are not established by Box<u8>/u8 probes.
N033/N034 recover the borrowed-shape callee/inverted/frame controls at opt1;
those semantic controls do not repair missing return-value Arbitrary support.

Process finding: N001–N019 did not execute the required frozen-workspace
metadata preflight before invocation. They ran dependency-free standalone
sources, offline, with the exact copied lock unchanged, but that does not
satisfy the literal per-run graph rule. No proof credit is assigned. From
N020 onward KNH_gate.py replays the exact frozen resolved graph (441 packages)
read-only in the existing retained metadata workspace before the standalone
probe, records all resolved features, and checks both locks afterward. The
shared workspace is never compiled into or edited. Adoption would require
fresh strictly gated replacements for any earlier evidence it intends to use.
