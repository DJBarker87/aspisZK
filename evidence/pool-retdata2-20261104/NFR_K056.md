# K056 isolation

Initial reproduction uses the byte-identical NFO_K056 patch, original names, deployed features and exact KMX patch. Further changes remove one assertion/input at a time. No credit until controls fail.

NFR_K001 reproduced both original failures: exit 1, wall 135.18141842307523 s, RSS 1805724 KiB, swap 0. Optimized deployed Pool, frozen graph unchanged. Patch bytes equal NFO_K056; no timeout or memory kill. Exact failure log retained.

Isolation tree so far (original harness/module names retained):
- K002 removes only AccountInfo assertion: AccountMeta assertion still FAILS.
- K003 removes only AccountMeta assertion: AccountInfo assertion still FAILS.
- K004 removes AccountMeta key observation from K002: readonly/signer flags PASS.
- K005 matched K004 control requires writable: FAILS at intended assertion.
No flags/key conjunction is being treated as a pass after dropping keys. Metadata key association remains OPEN.
