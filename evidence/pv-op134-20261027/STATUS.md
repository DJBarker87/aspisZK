# V230 / op134 stage status

Target not yet established. Branch codex/pv-op134-20261027, base 8483406290.

* Measured: pinned direct extraction refused, exact receipts and command in
  aeneas-op134-001 and charon-op134-001. SOURCE-BODY.json checks that the full
  shipped source file is the exact prefix of the prior extraction context.
* Proposed only: ROUTE-II.md. No shipped change, new prover-local Rust helper,
  verifier change, or new trust field.
* Checked so far: PV_Op134_Order, PV_Op134_Coverage, CellOrder00–10. Every
  successful receipt has standard axioms and zero swaps.
* Draft/queued: remaining cell order blocks, concrete inventory uniqueness
  and coverage, row materialization/order/dedup, bitwise masks/rows equality,
  reference bundle, dedup/OR and indexing lemmas. Do not count drafts as
  checked evidence. Per-module JSON receipts supersede this interim list.

Premise accounting: no deployed endpoint premise removed, added, or weakened.
V230's shipped-source link remains open. The existing op134_reference remains
byte-stable and reference-only; all PV_CBM_* files are checked against base.
The eventual new bundle quantifies over arbitrary base and callback dictionary
and retains the complete outer Aeneas Result and inner Rust Result.
