# Missing exact source snapshots

The first sequential C1/H1/G construction is recorded as using
`performance.rs` SHA-256 `e16d9faf45e40ad238a06ce79454217ba0eeddeb1e4741e192910850c30a65a9`
and `r17_c1_witness_audit.rs` SHA-256
`c846cbdbc280adec7aedd11e1187ec3cedb3ec83920d4b7aefa3bea815fbe555`.
Neither source snapshot remains locally or in the NUC candidate tree after
later overwrites. No replacement was reconstructed.

The locally available later `current-source` copies hash to
`4c575d4d1004bf39b0bb1f8069495e315e63a7ec9f423a60ec93f3487f4eb8b5`
and `1aa5c416fd971bb65bf5fd7aab20046a6e13c171dbaf272674337682f57f1a13`;
they are deliberately not offered as sequential-G source evidence.

For the per-column C1 follow-up, the preserved copies in `evidence/c1-source/`
match the recorded hashes: `performance.rs` =
`d6cb96979a96517280089dbde62b01353c6e6092f36140f9f142f7374ef18f9f`
and helper =
`2635d2ac9573d0d5f22c5b1216810eea84f7a636450207b26e9aea2827d2c3c5`.

The initially packaged root-level build3/build4 logs were earlier builds, not the matching final certificate builds. The matching NUC `logs/build-ledger.log` and `logs/build-initial-preserve-ledgers.log` have now been recovered, without rerunning anything. They record respectively exit 0, 11.74 seconds, 541,224 KiB RSS, zero swap; and exit 0, 11.05 seconds, 546,284 KiB RSS, zero swap. The earlier logs remain preserved. This resolves the apparent resource-receipt mismatch; it does not restore the missing sequential source snapshots.
