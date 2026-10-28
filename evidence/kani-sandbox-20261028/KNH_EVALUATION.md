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
