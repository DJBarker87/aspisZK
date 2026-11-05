# Owned scripts and validation

The NHB runner/gate/setup/native-source writer are copied into the NHK prefix,
with the assigned workspace and 70-attempt bounds. No shared infrastructure
is edited. The strict offline frozen-lock graph preflight and before/after
lock checks remain. NHK_GATE additionally records all resolved crate feature
lists (not only the root closure), a stronger evidence requirement; early
receipts retain the original selected-closure list and full graph hash.
Kani here targets aspis-core/r0 only; no verifier body is compiled by the new
membership harnesses. Deployed verifier feature parity on reused verifier
certificates is inherited from their pinned receipts, not newly measured.

NHK_EventChain/NHK_TraceBind are new source modules; reused NHB/NGQ modules and
objects are unchanged. Cache seed bytes/hash manifest and per-attempt resolved
Aeneas object hashes remain explicit. No extraction is launched.

After recovering a completed Kani receipt, the owned runner now records and
removes only files under its own NHK_tmp directory. This enforces timeout
scratch hygiene without touching the retained cache, sources, receipts,
shared directories or any running scope. Each attempt snapshots its inputs.
