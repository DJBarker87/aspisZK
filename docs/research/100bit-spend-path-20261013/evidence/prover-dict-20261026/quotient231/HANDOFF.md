# Source dictionary and quotient checkpoint

Branch `codex/cx-prover-dict-20261026`, base `4cd294bc606a713f9fa107bae8f116a1abdd6028`.
Target not yet established. No full store/retry/client carrier lift was continued.

| Obligation count | Before | After |
|---|---|---|
| Sufficient source fields |172 selected /83 open /255|175 selected /80 open /255|
| Historical full dictionary |176 selected /86 open /262|179 selected /83 open /262|
| Native lower types |26/28|26/28|
| Root headline premises removed |0|0|

| Entry | Ledger source subobligation | Installation theorem | Receipt |
|---:|---|---|---|
|78 fibre_point|V200|`R1Z.PDict_RemainingDictionary231.op78_installed`|`lean/23102-receipt.json`|
|231 trace clone|V248|`R1Z.PDict_RemainingDictionary231.op231_installed`|`lean/23102-receipt.json`|
|247 CT trace value|V255|`R1Z.PDict_RemainingDictionary231.op247_installed`|`lean/23102-receipt.json`|

The same selector extends the prior172-field source dictionary. Actual clone
and trace-value bodies were freshly extracted; fibre uses the read-only sibling
source bound in `sibling-binding.json`. Entry247 requires `ct-host-prover`.
No blanket native-world or allocation/Drop claim follows from source selection.
`PDict_RemainingValues231` supplies clone success/value and trace no-op laws
under the existing array/Vec models, with no supplied clone-success premise.

`R1Z.PDict_RemainingCaller231.client_independent` proves equality of the actual
`RealR1_client.prove_for_proof_accounts` functions, for all their arguments and
Result outcomes, when the three arbitrary raw callbacks are replaced before
source selection. Forty small selector commutation laws prevent hidden capture
by older selector layers. J23157: exit0,7.11s,4355192KiB RSS,swap0. This is a
fixed-carrier source result, not a native effect/trace or shared interpretation lift.

Retained: V268 native Error, V269 native Formatter, V270 forbidden Formatter-axiom
route (unselected), V271 File ownership/world; V262 generic coefficients/fromFn;
V263 WorkExtensional and all pv-cb-owned entries. No authoritative ledger file
was edited. No root/headline premise was removed, added, bundled or weakened.
The exact feasible-native invocation denominator remains unestablished.

## Native and extraction evidence

15/15 Kani runs:10pass,4timeouts,1unsupported actual-OS boundary. No Kani stub,
C ABI replacement, disabled safety/unwinding check, or backend patch was used.
Accepted checks cover simple/static/OS kind/retry projections, all17 R0 Debug
variants under every FormattingOptions value (bytes, failure, one call, options
and a64-bit sink frame), File flush/empty writes and NUL-path rejections,
and1024 fromFn call order plus pointwise u64 outputs. These are the stated
observations, not native Error/Formatter type installation or full File-world
adequacy. Allocated Error Display/message checks timed out and remain rejected.

Actual nonempty File::open is rejected at reachable foreign `open64`:
`native/pdict-q231-kani-043/stdout.log`. This is an unsupported construct, not a
mathematical counterexample. A required interpretation question remains pending:
does "no stubs" permit an explicit nondeterministic C ABI environment while
keeping real kernel/world association explicit? No permissive answer was assumed.

For255, actual generic core-array Charon extraction passes; Aeneas rejects
"Can't copy a mutable borrow" at `/rustc/library/core/src/array/mod.rs:155`.
Charon's MIR-stage flag only affects the current crate, not this dependency;
no unchanged failing dependency rerun or backend change was made. The u64 Kani
result is not promoted to the all-T native contract or another count removal.

## Verification and remaining work

59/100 Lean attempts:45accepted/14rejected;41 remain (next unused J23159).
15/15 Kani runs used. Refused admission labels are not compile/Kani attempts.
Exact source/dependency/time/error/axiom receipts are in `lean/`, `native/`,
`lean-summary.json`, `native-summary.json`. All successful axiom prints are
standard only. J23158 focused audit: exit0,1.71s,4305908KiB RSS,swap0,50standard-only
reports, including the unchanged conditional privacy headline and printed
RustProverRefinement. No package-wide frozen manifest or release/ELF rebuild ran.

`admission-timing-deviations.json` records early setup retries at140/166s instead
of180s. Both live gates allowed those scopes; neither produced accepted proof
evidence. These waits are explicitly not claimed compliant. Caps and launchers
were unchanged: Lean-M7000,6G/8G/swap0/Tasks128; native6G/8G/swap0/Tasks64.
One capped scope at a time. No memory cap or heartbeat/recursion limit was raised.

Next: settle the OS-world interpretation, then complete the owned native
Error/File-world and Formatter quotient associations and installation. For255,
finish a generic safe-reference/native association; retain its current premise
until that proof exists. pv-runjoin3 continues to own the effect-aware full lift.
No further zero-count carrier wrappers are proposed here.

No crates/programs, sibling worktree/source, simulator, observer, release pin,
key or authority changed. No merge or push. Task keys were not created or deleted.


Final consistency: all1252 dependency object hashes and all45 accepted own
source hashes match the focused audit. Every accepted module's compiled
transitive dependencies agree with the final audit inputs. All four raw
ProverRwFull source hashes match this worktree. See final-object-binding.json.
Kani0.67.0 uses Rust1.93nightly53732d5e0; the raw runner's ambient Rust1.94
label is separately qualified in kani-toolchain.json. This is not a release
compiler/ELF identity claim.
