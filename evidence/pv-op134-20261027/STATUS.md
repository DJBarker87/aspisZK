# V230 / op134 stage status

Target not yet established. Branch codex/pv-op134-20261027, base 8483406290.

* Measured: pinned direct extraction refused, exact receipts and command in
  aeneas-op134-001 and charon-op134-001. SOURCE-BODY.json checks that the full
  shipped source file is the exact prefix of the prior extraction context.
* Proposed only: ROUTE-II.md. No shipped change, new prover-local Rust helper,
  verifier change, or new trust field.
* Checked: all 60 cell order/bounds blocks; PV_Op134_Order and Coverage;
  PV_Op134_Inventory.ordered_bounds/nodup/complete; the complete Result
  PV_Op134_InventoryCallback.callback. The 3,803-cell reference inventory is
  now proved bounded, unique, free, and complete over the 1024 x 16 grid.
* Draft/queued: row materialization/order/dedup, bitwise masks/rows equality,
  reference bundle, dedup/OR and indexing lemmas. Do not count drafts as
  checked evidence. Per-module JSON receipts supersede this interim list.

Premise accounting: no deployed endpoint premise removed, added, or weakened.
V230's shipped-source link remains open. The existing op134_reference remains
byte-stable and reference-only; all PV_CBM_* files are checked against base.
The eventual new bundle quantifies over arbitrary base and callback dictionary
and retains the complete outer Aeneas Result and inner Rust Result.
