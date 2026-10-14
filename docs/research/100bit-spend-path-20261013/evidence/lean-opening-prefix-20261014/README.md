# Opening prefix checkpoint evidence

This bundle collects the focused capped NUC attempts for the 15 opening-prefix Lean modules listed in `source-manifest.json`. All 36 receipt-backed attempts have source snapshots whose hashes match their receipts. The final source copies match the successful attempt snapshots. The object archive contains the 15 compiled objects with member hashes and sizes recorded in the manifest; runner and environment snapshots are included.

Root independently audited the 36 attempt snapshots and resource receipts,
the 15 current sources and archived objects, all 13 supplementary source
hash sidecars, and the 76 axiom reports from successful targets. The 21
failed attempts remain recorded. Every successful report uses only
`propext`, `Classical.choice` and/or `Quot.sound`. No source snapshot needed
reconstruction. `ROOT-VALIDATION.json` records the audit and `SHA256SUMS`
seals all bundle files. No targets were rerun while collecting or auditing
this bundle.

The combined `R1OpeningPrefixCheckpoint-a` passed in 1.38 seconds with peak
RSS 3,530,180 KiB, zero swap and 38 axiom reports. Every target used a
4G/6G/0 high/max/swap scope on the pinned NUC workspace. Source base is
`beee9c934d2dd43ed9fe708c88036c1add2f541c`; the per-attempt source hashes
identify the changes being checked. All 14 central runtime fingerprints
remain unchanged.

This is focused component evidence, not a full protocol-security or
release-closure certificate. See [the bridge scope](../../OPENING-PREFIX-BRIDGE.md)
for the exact results and remaining obligations.
