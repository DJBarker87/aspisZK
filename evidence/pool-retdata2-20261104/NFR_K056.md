# K056 isolation

Initial reproduction uses the byte-identical NFO_K056 patch, original names, deployed features and exact KMX patch. Further changes remove one assertion/input at a time. No credit until controls fail.

NFR_K001 reproduced both original failures: exit 1, wall 135.18141842307523 s, RSS 1805724 KiB, swap 0. Optimized deployed Pool, frozen graph unchanged. Patch bytes equal NFO_K056; no timeout or memory kill. Exact failure log retained.

Isolation tree so far (original harness/module names retained):
- K002 removes only AccountInfo assertion: AccountMeta assertion still FAILS.
- K003 removes only AccountMeta assertion: AccountInfo assertion still FAILS.
- K004 removes AccountMeta key observation from K002: readonly/signer flags PASS.
- K005 matched K004 control requires writable: FAILS at intended assertion.
No flags/key conjunction is being treated as a pass after dropping keys. Metadata key association remains OPEN.

K006 fixes exactly one arbitrary input (meta=6) relative to K002 and PASSES: the newly appended verifier-checkpoint AccountMeta is correct. K007 matched key-corruption control FAILS at intended assertion. This narrows the trigger to preservation of existing vector entries; it does not alone distinguish reallocation from earlier copies.

Final configuration split, resume:
K008 no copy/realloc replacements: original metadata key assertion FAILS.
K009 matched key corruption in the same configuration: intended FAIL.
K010 applies exact KMX copy/realloc configuration, but unwind34 is insufficient
for KMX_realloc loop0; no semantic verdict or pass credit. The replacement
completes that finite stub loop at unwind512, without any time/memory cap change.
K011 control and K012 positive are the terminal comparison. Original module and
function names remain unchanged. Patch sha256 stays
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

K011 (on configuration, matched corruption, complete finite-loop unwind512)
timed out at90s: wall94.445582s, peak3449136KiB,swap0. It is NOT a failing
negative-control certificate and gives no pass credit. No unchanged rerun or
increased cap/time limit is authorized. K012 changes back only the claimed
positive key assertion to complete the requested comparison; any inconclusive
positive leaves this member UNISOLATED. No shipped behaviour finding follows.

## Terminal disposition: UNISOLATED

K012 positive with the exact KMX realloc/copy configuration also TIMEOUTS,
wall94.305015s,peak3539804KiB,swap0. No verdict flip is established. The pair
is inconclusive, not two semantic assertion failures, and cannot earn KANI COPY
RULE credit. A is stopped as UNISOLATED per the resume instruction; no shipped
bug claim and no new fidelity finding. K001/K002/K003 remain the observed
semantic failures; K008 is the final reduced failing original-name harness
with AccountInfo observation removed and arbitrary meta<7 retained.

Exact reproducible inputs: NFR_K008-shape.json and NFR_K008-NFR_native.patch
(no KMX replacement attributes); NFR_K009 matched corruption. KMX-enabled
positive/control are NFR_K012/NFR_K011 shapes and patches, respectively. Use
the per-attempt commands, graph/lock/feature checks and receipts; no source
renaming or own copy implementation. The retained harness is minimal along
the prescribed assertion/input-removal tree, not a claimed globally minimal
Rust program. Full AccountInfo association is likewise unresolved; passing
flags/appended checkpoint observations never discharge preservation of earlier
metadata keys or AccountInfo keys. No further A split is attempted.
