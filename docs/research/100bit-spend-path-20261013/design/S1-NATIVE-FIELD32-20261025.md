# Native prepared-claim field32 boundary, 2026-10-25

Target not yet established. This closes the native selected-record decoder
check on its canonical-frame domain, with no stub or replacement decoder.
It does not by itself remove weights.field from the parent claim harness or
connect the actual SDK/extraction/runtime/release boundary.

The exact frozen weights::field body and real WideExact::from_le_bytes,
from_limbs and CodeField implementation execute on a928-byte array. A symbolic
index covers every0–28 position. The selected32 bytes encode arbitrary eight
canonical native coordinates by explicit little-endian shifts; the other896
bytes are arbitrary. All eight returned limbs AND all four c0/four c1 native
M31 coordinates equal those same independently encoded words. First/last
position covers pass. There is no to_le_bytes/from_le_bytes roundtrip shortcut,
opaque decoder, transmute, callee stub or assumption instruction.

Classification: TOTAL on every928-byte input whose selected32-byte record is
canonical, at every valid index; not arbitrary-byte TOTAL. On noncanonical
records the frozen source unwrap can panic, so no contrary totality claim is
made. The pre-existing original_payload_y1_fields theorem supplies successful
canonical parser values for every reached S1 y1 column at model/source scope;
its concrete native/SDK transport is not silently assumed here. The parent
native constructor/claim check still has its explicit field cut until composed.

Freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a. Source-binding.json pins the
complete frozen weights file and exact field function. Only selected field
and imports are factored; the entire native core dependency source and actual
release feature/tool context are pinned by each input record. Production and
S3/S4/S5 tracks are unchanged. No source adoption or new source decision.

Source-only focused-extractor-proof-packet-v1 evidence:
evidence/s126-current-caller-20261021/s1-native-field32-20261025.
Exact commands, source revision e4555c7882 plus source snapshots/hashes, all
tool/import pins and pre/post checks are in attempts v1/v2. Kani0.67.0,
rustc1.93.0-nightly53732d5e0, optimized native arm64 target, one shared atomic
local compiler lock,4GiB sampled aggregate cap,180s guard. Only two warm local
packages; no broad replay, cold dependency closure, NUC or SBF operation for
this target. Default checks plus unwinding assertions, no initialization mode.

- Compile v1: exit0,0.451123458s,RSS251969536B,aggregate284786688B,swap0.
- Verify v2: exit0,4.260124834s,RSS842383360B,aggregate863322112B,swap0;
  0/306 checks failed,2/2 covers.
- #print axioms: N/A, Kani only; no new Lean theorem or axiom.
- Read-only checker passes32 source/evidence pins and scope checks.

S1/S6, actual SDK/account stage1 and the final100-bit source claim remain open.

## Later-build pin correction

These receipts retain historical component25866 pins. The current release
ledger identifies later build source4bb3b3f51e; see
[S126-FREEZE-RECONCILIATION-20261025.md](S126-FREEZE-RECONCILIATION-20261025.md)
for exact unchanged selected items and changed lower/core/adapter contexts.
No whole-release/source transport is inferred from these historical checks.
