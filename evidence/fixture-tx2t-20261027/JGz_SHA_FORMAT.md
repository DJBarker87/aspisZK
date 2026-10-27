# SHA certificate representation and capped preflight

Every message block is64 bytes, with16 native mathematical words,64 bounded SHA256 transitions and8 feed-forward additions. Message inputs, IV, compression outputs and final digests are checked against the inherited mathematical model and separately diagnosed with Python hashlib. No whole hash or large recurrence is kernel-normalized.

Groups C/U and P00-P27 use the inherited-style separate named word/register cuts. Before final aggregation, the object-size inspection showed over500MiB of selected SHA objects. This is cache size, not RSS and not a release measurement.

038 attempted local tables within a single block proof and hit default recursion depth at individual transition checks.096 split those local tables into8 named8-round proofs; individual local-table reductions still reached the default recursion limit. Both are rejected, with no proof credit.93 uses paired global word/register state cuts for P28-P56, with one named checked transition at a time. The smallest affected group P28 PASSES: exit0,27.977317116979975s,peakRSS4541760KiB,swap0; standard axioms only. The object remained about24MiB, so no object-size reduction is claimed. Limits were never increased. The proof is changed, not an unchanged failed replay.

No tuple-carrier/hash algorithm/input/round constant/result is changed by this representation. Consumers use only block input/start/result/checked and group chunks/lengths/folded; these interfaces are identical. The complete proof-hash bridge joins15 native data chunks and57 compression groups symbolically, keeping group chunks locally irreducible at the fold join. It does not expand a901-block spine or evaluate the whole recurrence.

The final import must itself pass inside the fixed cgroup/-M7000 cap. Cache-size estimates are not substituted for that evidence. All larger consumers remain pending until their own accepted receipts.
