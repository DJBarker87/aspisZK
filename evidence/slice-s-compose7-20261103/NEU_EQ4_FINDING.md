# Four-byte comparison boundary

K005/K007/K008 timeouts are excluded, not counterexamples. K008 isolated
`header[..] != RESULT_MAGIC` (slice versus fixed array) with arbitrary4 bytes.
The already composed NEQ_K087 header helper executes `bytes[..4] != magic[0..4]`
(slice versus slice), and has a passing full216-byte-domain parser check plus
matched controls. Its success is retained unchanged.

These are different trait/interface shapes. This job does not silently replace
the frozen request/emission slice-versus-array comparison with the passing
slice-versus-slice helper, nor promote that helper to a new callee. A future
native association must prove the actual array-to-slice wrapper/domain at the
real call site, with its full ordered Result/frame and matching control, then
reuse the existing slice comparison law if the pinned source proves it is the
same callee. Otherwise it remains a slice-boundary obligation. No longer solver
timeout, renamed harness, new trusted comparison or SHA model is proposed.

The native request cuts K011/012 and K021/022 keep the relevant comparison
replies explicitly arbitrary. They do not discharge this boundary. This finding
does not affect the admitted NEQ require_header packet or establish a tool bug.
