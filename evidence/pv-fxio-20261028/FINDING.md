# FXIO-1: a fixed pure dictionary loses the repeated-create world change

Status: proof/native receipts pending. No row closure or native counterexample
is credited until both are recorded below.

## Precise affected claim

A single fixed `ProverRwFull.ExternalFuns` dictionary, on the original emitted
store carrier with its other fields unchanged, cannot reproduce the complete
native filesystem outcomes of two repeated reservations. This is a source
association obstruction, not a privacy attack or a claim that Rust create_new
is incorrect. It is stronger than a disagreement with one chosen owned copy:
the complete-result contradiction quantifies over *every* pure callback and
fixed decoder on the same argument values.

The source of the obstruction is the original emitted callback signature,
not Kani or a replacement syscall implementation. At op22 the fixed options
and path yield one fixed outer Result. In native execution the first call
creates the entry, so the second call with the same options/path reports
AlreadyExists. The emitted reserve_fallible source clears last_error and
returns the same directory field on success. A subsequent call with the
returned store and same nonce therefore cannot obtain a different filesystem
world from that record. The filesystem contents are external mutable state.

## Evidence and limits

- `original-signature-binding.json` pins the actual op22 signature and the
  full original emitted reserve_fallible definition at the candidate source.
- `native-source-binding.json` binds the fixture's 681-byte reached suffix
  byte-for-byte to the shipped Rust. The fixture supplies the previously
  computed path and keeps only self.directory, the sole self field accessed
  in that suffix. No hashing, whole-store or whole-client refinement is
  asserted. Last-error reset precedes the suffix in both relevant executions.
- `stdlib-structural.json` and retained source files pin nightly-2026-06-01's
  wrapper chain through `open64`, O_CREAT|O_EXCL and errno-to-kind dispatch.
  This is partial **structural (K-1 substitute)** evidence, not a universal
  proof of any OS syscall or of every Error.kind case.
- `PV_FXI_RepeatCreate.lean` has an explicit inhabited filesystem reference
  with path, descriptor, contents, persistence flag, entry existence and
  error-code schedule. `no_fixed_complete_result` rules out a common fixed
  projection of the complete callback result at the two checked worlds.
  It does not equate the arbitrary descriptor marker with a native fd and
  does not interpret the full original extracted function in Lean.
- Native validation compares the first/second booleans with the reference
  entry-existence transition and checks AlreadyExists, errno and unchanged
  80-byte contents. This is **finite validation**, not universal OS evidence
  or crash-recovery evidence.

The original all-world fixed-dictionary interpretation is the refuted claim.
Neither the existing conditional privacy theorem nor every possible
world-indexed/effect-aware interpretation is refuted. In particular an
explicit world interpreter can model this behavior; its composition with the
original caller remains an actual P proof obligation.

## Required repair

Carry and consume one filesystem world across the entire selected caller,
including open/create errors, partial writes, sync, and owner Drop. A separate
per-call world-indexed dictionary is insufficient unless its caller-level
threading and transport are proved; silently reselecting dictionaries changes
the fixed-dictionary statement. Re-extraction/instrumentation or a proved
stateful interpreter is a proposed next deliverable, not a theorem supplied
here. No source changes under crates/ or programs/ are authorized by this job.

The adopted observation equality transfers already-defined extracted outcomes
and state to native observations. It does not supply the missing state
transition or excuse erasing the difference between the two native outcomes.
T is unchanged. See OS-CONTRACT.md for each row's exact coverage and potential
additional atomicity/durability facts requiring owner consideration.
