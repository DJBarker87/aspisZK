# Kani harness edits are not merged into the frozen source (lead, 2026-10-27)

leaf-p6-1 added #[cfg(kani)] harness modules inside the shipped crate
aspis-r1-cost-probe (14 files under crates/: new LPa_*.rs files and
cfg(kani)-gated `mod` declarations in candidate.rs, compact.rs,
fast_pairing.rs, r1_semantic.rs, r1_wire.rs, sampler.rs, verifier.rs).
None of it is compiled in a non-Kani build, but the files are part of the
frozen release source (D188 extraction pin, the 7,978-file release hash set,
the client pin), and the three-ELF rebuild that would confirm the pins
failed on a host resource limit (rust-lld, TasksMax). The lead therefore
merged the proofs and evidence ONLY. The harness edits are retained as
LPa_kani_harness.patch (sha256 in LPa_kani_harness.patch.sha256). Every Kani
result in this directory is a statement about "frozen release source + this
cfg(kani)-only patch", which is the P6 form: the patch adds harnesses and
changes no non-Kani token. Re-running a bridge means applying this patch in a
scratch tree, never to research.
