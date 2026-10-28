# Own script repairs

Setup f-string brace escaping was corrected after the frozen source archive
upload but before the first prover launch. Setup resumed on that archive.
K001: Rust module lookup required explicit #[path="NDB_native.rs"].
K002: Skip<slice::Iter> has no as_slice; arbitrary iterator pre-state now uses
slice[k..].iter() so its remaining suffix can be compared. Both failed compiles
are charged. These are own inputs, no host/lead infrastructure edits.

NDB gate is the NCV strict frozen graph/lock/feature validator with its own
namespace and workspace paths. Full graph checked before each selected exact
harness, offline, lock hash before/after. Source snapshot includes KMX patch
hash and default deployed verifier program features. Rust optimization=3;
scopes 6G/8G/Swap0/Tasks64. No Box/slice/Vec stub_verified substitution,
Option<fn> or field-multiplication stubs are used.
