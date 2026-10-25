# L186: stopped on extraction-source mismatch

Branch: codex/cx-lowering-20261026. Audited research/source revision:
14668ba43975d2078f431c126bb728952e29b56a. **L186 remains OPEN; target not yet
established.** No premise removed, added, weakened or reassigned.

The owner completion rule says to stop on a mismatch. The first S2W extraction
receipt supplies one: evidence/s2w-20261023/charon-001/receipt.json,
/source_hashes/src~1programs~1r1-cost-probe~1src~1r1_pool_adapter_owned.rs.

- Extraction pin: 11e4a5e3ea31795b0c55fe5c22d74ffb7496454c1307112004b6a69be55fb628.
- Current source: 246d96b479ef552b485a51a2a3d4c4dbe1ff4ef9c0527b6f9a872f296b60576b.
- Current source size: 20485 bytes.

The other four source pins in that receipt match current files. The independent
source-inventory.json repeats the old pin. d189-inherited-source-delta.json
already documents this change and explicitly distinguishes historical artifacts
from later H5 artifacts. Commit 60cb14bde27c219709a90beff94f21c1310e2d15
changed require_zero from an indexed loop to a tail-slice loop. The D189 audit
uses the current hash; its existing helper equivalence qualification is retained.
This finding is an exact-file identity failure under this job's criterion,
not a new counterexample to that helper theorem or a claim of a shipped bug.
Historical receipt success is not reassigned to the current file.

## Validation and receipts

Run from the repository root:

```
python3 evidence/lowering-20261026/Low_check_source_pins.py
```

Expected exit: 1, status mismatch. Low_preflight_manifest.json pins the original
receipt. Low_source_pin_check.json records each compared hash and evidence JSON
pointer. Low_check_receipt.json records exact command, checker hash, dependency
fingerprint, source revision, exit, wall time, peak RSS, swaps and axioms status.
This is a lightweight local Python hash check, not a formal release result.
No theorem was added; #print axioms is N/A.

The checker deliberately stops after the first mismatching evidence receipt.
It is a reproducible failing preflight, NOT the requested complete source-to-ELF
manifest. Op3I/Op4P/Tx2I/Op5T/SdkC/SdkD/Tx1Q/WAdm/Tx2N/CPhy/T2Nat/AuS1/GExp/GExq
coverage has not been established. No compiled dependency closure is claimed.

## Remaining work

Owner resolution must supply coherent current-source extraction/certificate
association while preserving historical evidence. Then finish the full
certificate-source inventory, rebuild all three pinned ELFs on the build host
using the pinned toolchain/features and caps, and rerun the existing S10 tool
for all 140 ordering certificates against those rebuilt ELFs. The existing S10
ruling retains P7 and does not create a Lean lowering obligation.

No host job launched; SBF 0/6, Kani 0/0, Lean 0/10. No ELF hashes were newly
verified and no S10 ordering check was rerun. No crates/, programs/, existing
Lean modules, other worktrees, keys or artifacts were changed. No pushes.
