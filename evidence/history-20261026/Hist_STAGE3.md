# History stage 3: causal loader, source admission and actual-source fixture

Hist_CausalBinding.version constructs the actual saved/loaded-indexed history
on Hist_RuntimeEntry's computed ledger loads and commit. The source's own owner
check is proved under concrete documented pure public-key equality; other child
slots are unchanged. Hist_SecondSnapshot.on_cuts derives the actual selected TX2
checkpoint's bytes from account6's computed snapshot. The same-key association
is EXPLICIT, at the runtime-experiment boundary. No source check tying two
independently supplied TX1/TX2 keys is claimed. This constructor is not declared
a deployed complete instance merely because it compiles.

Hist_Asq8Guards.guards, Hist_ValidateCut.authenticated and Hist_Metadata prove the
actual source account-guard path: Pool master/forest checkpoint/lane authenticate
under Pool ownership, while the distinct slot6 verifier checkpoint authenticates
under verifier ownership and readonly/nonsigner/nonexecutable checks. Pure key
equality is a concrete library interpretation, not a hash injectivity premise.

Hist_Nonvacuity constructs an initialized1768-byte local checkpoint and a nonempty
history containing an authorized foreign write plus rollback. This is local
runtime-model non-vacuity; no new jointly accepted cryptographic fixture is
claimed. Earlier broad simp on replicate1767 hit recursion depth at044;046 uses
symbolic length/head lemmas instead. No depth/heartbeat cap was raised.

Actual-source fixtures:
- Hist_RUST001 passed2tests,43.073s,587348KiB,swap0, but initially used fresh
  transitive package resolution. Not production-lock evidence.
- Hist_RUST002 passed2tests,16.180s,457604KiB,swap0, after replacing the lock input
  with production Cargo.lock. Hist_lock-check.json verifies all189 selected
  dependency packages match production versions/checksums, no added external
  package. The fixture root package alone is added. Both execute the unchanged
  real shipped release entrypoint: initialized checkpoints reject for both
  splits and lifecycle tags reject before account inspection. These are concrete
  negative fixtures, not exhaustive accepted-source refinement.
- Hist_KANI001 STOPPED before verification: zmij build-script link aborted with
  std::system_error: Resource temporarily unavailable, lld/collect2 signal6.
  Exit1,7.508s,419028KiB,swap0. No proof pass/counterexample. No unchanged rerun,
  cap change or host/launcher repair was performed. Independent Lean path works.

All Rust/Kani commands ran optimized in the task's own host directory, capped
6G/8G/swap0/tasks64 with four Cargo jobs. Runner is an unchanged copy of the
existing runner; no infrastructure was built or modified. Hist_host-source-check
confirms all8 selected shipped source/lock inputs match this branch and the
retained source/pin audit. No shipped/cfg(kani) file changed, so no ELF rebuild
trigger. The fixture and cfg(kani) harness are proof-only evidence sources.

Ledger delta: removed NONE globally, added NONE to deployed endpoint. The
same-key/runtime trace association and whole-containing-source oracle experiment
remain uninstantiated, so L094-L098/L180 are not claimed closed. The remaining
budget is used for concrete same-witness composition and source association;
no replacement structure is counted as discharge. Current validation through051:
51 charged Lean submissions (49 actual processes +2 predecessor prelaunches),
1 Kani submission (compiler failure),2 optimized Rust fixture runs. Standard
axioms only in every accepted theorem; failed source snapshots excluded.
