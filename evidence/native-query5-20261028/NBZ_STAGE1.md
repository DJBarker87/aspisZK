# Stage 1: matched controls in flight

All 24 asserted NBW replay cuts receive a matched negative control. Each is an exact prefix-renamed native harness with one false expected value, unchanged input assumptions, unchanged unwind and unchanged stub attributes. Positive source/helper definitions remain unchanged. NBZ_CONTROL_PLAN.json lists each original/false assertion and positive receipt. NBZ_controls.patch retains the scratch-only module; the exact upstream KMX payload remains unchanged, SHA-256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; stubs SHA-256 ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.

The requested nineteen is corrected: the six existing negative controls are KMX primitive tests, not matched to any of the twenty-five replay rows. none_mark_native has no post-copy assertion (no copy-result credit is requested for it).

Runner validation repair: the own batch requires exit 1, an explicit `Failed Checks:` result and no `CBMC timed out` before treating failure as a negative-control result. Compiler failures and timeouts never count as a failing control. This strengthens the inherited driver classification; no host infrastructure changed.

Cache imported hashes: NBZ_CACHE_START.json. Scratch source reuses the lane's NBO tree via a symlink, adds only NBZ_native cfg registration/module and leaves all NBW/NBO/KMX modules unchanged. Frozen lock hash checked before metadata and after every Kani invocation. Metadata and Kani each have fresh admission, and scopes do not overlap.
