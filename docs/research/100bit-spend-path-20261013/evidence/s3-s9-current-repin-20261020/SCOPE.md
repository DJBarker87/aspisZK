# S3/S9 current-source repin (2026-10-20)

Status: in progress; source correspondence and focused Lean checks are not yet closed.

## Scope and baseline

- Branch: `research`
- Baseline revision: `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`
- Current selected source: `crates/aspis-r1-cost-probe/src/weights.rs`, SHA-256 `30e8f10fa7f0adfe2101bb5df8bdfe0876ee70b35349ab886ab4dc30a0d16cca`.
- Related source pins: `transport.rs` SHA-256 `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7`; `aspis-core/src/r0/opening.rs` SHA-256 `349dc999c1165e9e3be07a840ce99dc7a0b567c7a0545088baea80894476ee7d`.
- Existing generic algebra owner: `lean/S2LibraFactoredIdentity.lean`, SHA-256 `3344c8c59038898ab49e91c76fd785c5fe796c0ab43bc48908c0a55c6d2d5674`.
- Existing range owner: `lean/R22ControlBounds.lean`, SHA-256 `c77a94f6c87d9d8c00d13445a189214006865962f57fedb878382c620c968bad`.

## Candidate history

Candidate3's pinned weights source (`d631a90ec`) has SHA-256 `4495a7efa2b80f40ee61118eb688d7525816b062e511168f3bf07d0afcf51bd9`; current source differs by the later candidate14 S9 addition. Candidate14's pinned weights source (`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`) matches current byte-for-byte. The candidate3 and candidate14 declaration inventories reported no extracted Lean bodies for S3's grouped classifier or S9's factored helper. Candidate evidence remains historical and is not current-source proof.

## Current proof boundaries

`S2LibraFactoredIdentity.original_eq_factored` / `source_scaled_eq` establish the generic 56-entry algebraic factorization, including zero challenges. They do not prove a Rust/extraction simulation. `R22ControlBounds.weights_digits` proves `16*j+s < 1024` for `j<64,s<16`; `libra_indices` proves quotient/remainder ranges for `index<56`. Neither theorem connects current Rust bodies to a checked Lean model. The S3 table-to-`Variant::row`/`COPY_ACTIVE_ROW_MASKS` finite classification bridge is also unproved at this point.

No source or shared document outside the assigned candidate/evidence directories has been changed.
