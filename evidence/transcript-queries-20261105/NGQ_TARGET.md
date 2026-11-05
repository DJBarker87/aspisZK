# Frozen target and evidence classifications

Source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. The558 scratch-input files
(including all crates/programs files used) are byte-identical before cfg(kani)
instrumentation; NGQ_RELEASE_IDENTITY.json records the hashes. The repository's
shipped crates/programs are untouched. Harnesses exist only as evidence text,
a patch and host-owned scratch modules. Frozen lock5782e6a3… is copied before
metadata; each Kani gate compares package tuples and resolved edges offline,
then checks the unchanged lock. Metadata may use --locked; cargo-kani does not.

Parameters:22 ordered distinct surviving18-bit words,64 maximum draws,8 blocks
of32 bytes,8 advance replies,8 little-endian words per block. Transcript absorb
encodes [old32 state, [0,160+row], little-endian u32 payload length, payload].
Native absorb domain: row<=95 and payload<=8192, covering the named preparation
query rows30/31 and S1 final8192 bytes as well as S2/D final2048 bytes. This
coverage is input-shape evidence, not an unconditional caller-domain theorem.
Other pair/window domains cover all32-byte states/replies and arbitrary complete
8x32 frames; scan-step domain len<=22, draws<=64. Constructor totality covers
all rawU32, exceeding the masked sampler output domain.

Deployed native verifier features: private-leaf-salts, optimized-terminal,
program-build; no prover. Core-only helpers use r0, the same core feature set
in the deployed dependency closure, and have no cfg-dependent body. The caller
trace arguments remain evaluated with prover disabled. Each gate pins features,
compiler invocation and graph. Tool versions/pins are in NGQ_E001-extraction-pins,
per-attempt source receipts and NGQ input manifests. Lean4.32.0, Aeneas objects
selected by LEAN_PATH are hashed in every receipt; legacy NBA copies are retained
in the owned cache but not selected by the NGQ-prefixed proof imports.

All scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64, Lean-M7000;
one own scope at a time. Native verification uses optimized Rust, one build job.
Each receipt records target, exit, wall time, process RSS, cgroup peak, swap,
source revision/source hashes, command, features and axioms (N/A for native).
Parent process RSS must not replace the cgroup peak on launcher timeout.

Formal model proofs, native finite verification, source-fission validation and
inherited realization are separately labeled. No full cold release replay is
claimed. No source change invalidates or requires rebuilding the inherited ELFs:

* default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
* devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
* Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

These are inherited artifact pins, not hashes from a new ELF build. Runtime
SHA=H, accepted runtime trust rows, P6/D188 option-A semantic transport,
compiler/ABI/Std/allocator/Aeneas/source-to-ELF and cryptographic assumptions
remain. No trust item is removed; no100-bit per-attempt bound, privacy property
or two-transaction design is changed.
