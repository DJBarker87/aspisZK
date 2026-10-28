# Retained failures

K001: owned runner omitted deploying the immutable S2W_run_host.py into the new owned workspace. Admission succeeded and a terminal systemd scope ran Python, which exited2 before any Kani/compiler launch. No proof receipt exists. Launcher log and unchanged after-lock retained. Fixed OWN runner to install and byte-check the existing backends from NBC_LAUNCHER_INPUTS; shared host infrastructure untouched. K002 is the first actual Kani submission. This is a missing-input repair, not a timed-out or memory-killed proof rerun.

K002: setup-only JSON decoding error in own validation wrapper; no scope or Kani launched. Corrected serialization and added reverse dry-run verification to recognize the already-applied, byte-identical K001 patch. Validation is stricter than filename-based skipping.

K003: Rust lifetime compile error caused by a static raw pointer whose pointee contained a borrowed slice. K004 changes only the observation pointer to erased *const (); it is compared but never dereferenced. No Rust production source change. No solver launched by K003.

K004: the own patch preflight used patch -R --batch, which automatically reverses direction and misleadingly accepted an unapplied patch. The intended lifetime edit was not installed, and the same compile error recurred. Replaced preflight/application with strict git apply --reverse --check / git apply (no automatic reversal). No solver ran.

L001: residual pair let-pattern reduction after the Result rewrite; L002 adds the final definitional reduction. Rejected sorryAx diagnostic excluded from evidence.
