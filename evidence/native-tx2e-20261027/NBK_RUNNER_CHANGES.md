# Own runner changes

NBK derives from NBH controllers, raising only this job count to the authorized 60 Kani budget; caps and timeouts unchanged. Kani accepts no --locked; pre-run cargo metadata uses --locked --offline and exact LPm frozen package/edge equality, before/after frozen lock hashes, CARGO_NET_OFFLINE=true.

Validated cargo-metadata raw stdout stays on host. Local receipts retain SHA256, size and location plus graph match; transport logs hash large payloads rather than duplicate them. This bounds local evidence volume without changing admission or graph validation. Lean and native controllers use unchanged S2W launchers and S2H admission. Failures stop batches. No timed-out shape is rerun.
