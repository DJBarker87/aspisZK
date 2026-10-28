# Native stub inventory

No field-arithmetic stub is used, so the LPh arithmetic (stub,theorem,domain)
obligation table is empty. No SHA/runtime digest or decoder replacement is used.
No stub_verified Box/Vec/borrowed-slice result is used.

The only replacements are the exact KMX copy/clone/to_vec/extend/realloc functions
from evidence/kani-mitig-20261028/KMX_copy_stubs.patch, SHA256
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Rust stub SHA256 ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
K002 positive and K003 negative establish the local copy control configuration.
Every native pass also has its own matched output/control inversion. K027–044
selected no harness and have no credit. Full-buffer timeout shapes are retired.

KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame are imported read-only from the
pinned cache. NCV_CopyFrame proves arbitrary-offset association, disjoint-window
commutation and outside framing from those laws. Pointer validity, non-overlap,
length, allocation and actual source-call/window association remain caller
obligations; this value composition is not a full native decoder bridge.
