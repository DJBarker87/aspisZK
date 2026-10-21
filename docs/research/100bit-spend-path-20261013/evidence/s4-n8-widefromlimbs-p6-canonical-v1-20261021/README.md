# S4 N8 canonicality into wideFromLimbs

This packet removes the free canonical-values premise from the callback bridge. The general theorem asks for exact same-input P6 field agreement: raw ops.arrayFromFn on the callback trace equals P6 N8 execution using the retained current reducer. The trace success therefore gives the same P6 result, and the existing actual-reducer theorem establishes every returned word canonical.

The public withP6CurrentReducer adapter installs the current reducer and P6 N8 execution. Its field agreement is proved by rfl, and the adapter specialization needs only the explicit wideFromLimbs-to-EbyK binding. This is a Lean model adapter, not proof that frozen Rust Std was installed.

The selected repaired Fmt object is 63b8efa...; the earlier v2 callbridge attempt selected stale 7c17a7af... and leaked core.fmt.Formatter, retained under diagnostics.
