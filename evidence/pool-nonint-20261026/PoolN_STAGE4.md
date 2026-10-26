# Stage 4: split guards, rejected broad prefixes and axioms audit

KANI025/026 pass the actual native load_canonical_pool_state and
CanonicalPoolStateV1::decode_account_from_program_invariant guards for arbitrary
checkpoint bytes, balances and public keys at192/1768. Expected errors are exact;
these split probes check the first byte and balance, not a universal whole-array
frame. KANI029 checks the actual master decoder in readonly mode. KANI027/028/
030/031 strengthen fresh/payer/marker/plan guards to arbitrary signer/writable
flags and public keys. Their complete receipts and cover counts define scope.
They do not assume a successful decoder or native caller to force a result.

KANI032/033's actual ASPT prefixes both timed out, including canonical fixture
and then fixed correct metadata replacements. Neither is rerun unchanged. The
remaining planned broad prefix jobs were replaced by isolated actual guards,
not reported as successful handler prefixes. No arbitrary-instruction, other
handler or all-role closure credit is taken from those replacements.

PoolN_LEAN009 is the single focused axioms audit: imports all four current new
modules and prints all12 added theorem targets. Only propext, Classical.choice,
Quot.sound, or no axioms. No package replay or unchanged regression. Receipt009
pins the exact imported objects; current source hashes are matched to their
own green receipts by final validation. LEAN008 is the green nonvacuity source;
failed006/007 error elaborations remain rejected.

PoolN_host-overlay-pins and final-host-overlay-pins compare all133 inherited
Pool compiler inputs against the actual copied host workspace: frozen production
prefixes plus exactly named cfg(kani)-only suffixes. No shipped repository input
changed and no ELF rebuild trigger fired. Inherited verifier/default/devnet/Pool
pins are not relabelled as new builds. The tests use the owned PoolN source/cache
copy, the coherent SInt2 Lean cache, and existing unchanged capped launchers.
No new launcher, library contract, lifecycle trust item or host cap was added.

Time in the Rust/Kani jobs is expected in CBMC symbolic execution/proof search;
optimized Cargo compilation is typically a few seconds. No dense field
elimination, arithmetic release gate, certificate build or SBF rebuild ran.
