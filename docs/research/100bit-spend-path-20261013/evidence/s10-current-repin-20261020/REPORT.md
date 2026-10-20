# Current-source S10 inventory — 20 October 2026

Status: **OPEN**, source inventory only; no new soundness theorem or re-extraction is claimed.

Pinned revision: `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`. The required command with `--require-complete` ran to completion and exited **2**, correctly rejecting incomplete correspondence. Results: **281 unchanged, 41 re-extracted, 1 authorized helper replacement, 29 unresolved** within the registered historical/current cones. These are declaration records, not independent proof obligations.

The first attempt failed before writing an inventory: `reconcile_followup_statements` tried to append to `identity_basis` on an unresolved source row. The fix preserves unresolved Rust correspondence even when retained generated Lean is identical, records the Lean comparison without promoting it, and retains the valid unchanged promotion when Rust identity is established. `check-reconcile.py` covers both cases and passes. No compiler or Lean replay was run for this inventory.

The 29 unresolved rows are in `unresolved.json`: current wire/error carriers, changed Prepared construction and claim, retired tx1/finish caller bodies and program first. Error-carrier source identity must be re-established too; matching semantic branch names alone is not a current type pin.

**Registry limit:** this tool enumerates retained accepted/current registered cones. `candidate.rs`, `compact.rs`, `multiproof.rs`, `fast_pairing.rs`, `fast_dots.rs`, `weights.rs` have no entries in that historical registry. Their current extractions must be registered before S10 can mean the whole adopted verifier cone. Passing the old registry alone would not close S1–S9 or the adopted-format source correspondence. The eight-way code is historical/audit-only and must not be substituted for these missing cones.

No declarations are newly re-pinned by this packet; the inventory identifies retained identities and outstanding work. No overflow lemma is added by this packet. The parallel S3/S4/S5/S9 packets own arithmetic source re-pins and range joins.

The next stage-2 borrow fix reopens source pins and declaration correspondence for its changed `verifier.rs`/`candidate.rs` bodies and their callers; it does not invalidate unchanged field arithmetic merely because a parent file hash changes. Stage-2 S8 waits for the assigned cx-stage2b generated Lean. Current pins in this packet are a working baseline, not the final combined release pin.

R5 distinction: the retained sixteen-byte strict field parser theorem is not a parser for the 57,607-byte stored proof. Logical `decode_k` still reads the low sixteen bytes of each reconstructed 32-byte value. Source identity of that leaf and the compact expansion/check/strict-prefix caller composition must be tracked separately. The new expansion/caller theorem remains open.
