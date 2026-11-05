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

After NHK_K012's native full-window split timed out, the local split-campaign
queue was stopped while its already-submitted K013 child continued unchanged.
No host job was interrupted or resubmitted. Recover K013 through its live
owned runner, then schedule the smaller native windows before more parent
composition gates. The queue stop changes scheduling only, not validation.

Future native window/split harness generation constructs the22-cell arbitrary
array from22 independent scalar kani::any calls. This preserves the complete
input domain and avoids an unnecessary aggregate return copy at harness setup.
It changes no native contains body, reference predicate, assertion, bounds,
stub, cap or timeout. Already submitted source snapshots remain unchanged;
matched controls use the identical generated source. No new copy stub exists.

After arbitrary-offset width3 timed out, the remaining arbitrary-offset queue
was stopped locally. Submitted K017 (width4) finishes unchanged and is
recovered once. Next isolation fixes the physical window start to the caller's
actual prefix start, eliminating arbitrary-offset pointer selection. The
reference is still split into both contiguous windows; no domain is silently
replaced by a short prefix and no timeout/cap is increased.
