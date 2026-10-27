# Private source and object overlay

No shared env-J sources are written by this job. The existing run-joint.sh
is reused as a private copy with ONLY SRCROOT and OBJ changed to this job's
host directory; its env J, caps, lock/admission, timeout, global sent-input
ledger, and global attempt receipts are unchanged. The exact script is under
tools/pv-op134-20261027/run-joint.sh. run2.py and the tools are unmodified.

The previous cbmid job has no surviving private lean-objects directory.
The shared R1Z object directory was hard-linked read-only into this job's
private objects/R1Z. No source was copied into the shared tree. New modules
use PV_Op134_ and write only their own new object names.

Attempt 50000 failed before elaboration: Lean resolves the R1Z directory
from the first root, so the initially empty private root hid the shared
PV_CBM_InventoryShape object even though the preflight had found it later.
50001 was refused as duplicate (uncharged). Copying the existing dependency
objects changes the environment; the import fingerprint now resolves the
actual private object paths, rather than reporting the shared fallback.
50002 was refused by the 55 GiB aggregate reservation (uncharged); the
required 3-minute cooldown is observed. No caps or launcher ranges changed.
This is focused evidence against restored objects, not a coherent release
replay; direct object hashes are retained per run.

50003 then exposed a broken pre-existing Aeneas symlink in the earlier
commit54 env-J search root (its target backend directory was deleted).
The rebuilt shared object tree has real Aeneas objects. Its existing objects
were hard-linked into the private overlay with no-clobber, so the effective
first root now supplies the rebuilt dependencies instead of the broken
historical links. This is object reuse, not a dependency rebuild or a repair
of shared infrastructure. No symlink in any shared root was changed.
