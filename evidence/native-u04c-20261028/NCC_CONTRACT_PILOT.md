# Contract pilot

PILOT RESULT: **USABLE for the tested pure Bool/record interface.** All three
required controls fail semantically in the pinned configuration. This is evidence
for these exercised contract mechanisms, not a general Kani soundness proof.

| Test | Receipt | Observed result |
|---|---|---|
| (a) actual getter wrapper, deliberately inverse ensures | NCC_K035 | FAIL 1/49 at the inverse postcondition |
| valid weak contract of actual getter wrapper | NCC_K036 | PASS |
| actual weak wrapper body, exact-bit caller assertion | NCC_K037 | PASS |
| (b) same assertion under stub_verified, True postcondition | NCC_K038 | FAIL 1/19 at assertion panic |
| actual two-byte write body baseline | NCC_K039 | PASS |
| (c) declare only a mutable, write a and distinct b | NCC_K040 | FAIL 1/60, *var_4 is not assignable |

NCC_PILOT_CONTROLS.json verifies identical source hashes, semantic environment,
limits and tool binaries for these six runs. Kani 0.67.0 binary
683f3ad1216e67686a39b2fcd6dc661f5090574f55fde9dd407966dca42cbfad;
CBMC 6.8.0 binary decfbd8336c557f663d539b3bb4b12aac3396009d616810d325bcd8b42b8a973.
Each run uses -Z function-contracts, -Z stubbing, optimized Rust, the exact KMX
patch, fresh complete frozen-graph validation offline, unchanged lock, 90-second
solver gate and 6G/8G/swap0/tasks64 scope. No timeout/memory kill/cap increase.
Wall, RSS, swaps, revision, hashes, command and N/A axiom audit are in each receipt.

K038's assert_eq failure is rendered through core::panicking::assert_failed_inner
with Kani's runtime-formatted-message placeholder. The output is retained. The
same exact comparison succeeds on the actual body in K037 and fails only under
replacement in K038; the valid weak contract is independently checked in K036.
This is a semantic assertion failure, not a compiler error or unwinding failure.

The next test proves a contract on an ACTUAL native getter and exercises the
unchanged native validate_verifier_registry_v1 caller under that verified
replacement. This private validator is not the SDK authentication caller at
op26. Its success cannot discharge that separate extraction component.

Reference for syntax only: [Kani contracts documentation](https://model-checking.github.io/kani/reference/experimental/contracts.html).
All result claims above come from the retained pinned receipts.
