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
