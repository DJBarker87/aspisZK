# Native verifier hash-input measurement

The optimized NUC driver accepted tx1 and tx2 of the saved P3 S2
`transfer-1023-os-task` fixture with k=11. It counted each complete
concatenated `HashFn` input using that byte vector as the map key.
SHA-256 annotations are not the identity used for counting.

| Scope | Raw calls | Distinct byte strings |
|---|---:|---:|
| Tx1 | 349 | 297 |
| Tx2 | 234 | 179 |
| Combined | 583 | 452 |

There are 24 distinct inputs shared by the phases. Thirty exact inputs
repeat somewhere in the run, accounting for 131 calls beyond first use.
The checkpoint contains 1,768 bytes. Public statement decode/re-encode
roundtrip and both verifier acceptances are asserted by the driver.

`execution.json` records commands, source and fixture hashes, toolchain,
resource preflight, and prior counter-local failures. The final cached
release build exited 0 in 0.35 seconds with 185,924 KiB peak RSS; the
verifier exited 0 with 4,224 KiB peak RSS and elapsed time below the
timer's displayed resolution. Both used 4G/6G/zero-swap cgroup limits.
`ROOT-VALIDATION.json` records source/fixture/artifact hash checks and the
independently checked repeat arithmetic.

The driver is `tools/r1-hash-input-counter/`. No proof was generated and
no verifier/prover source changed. This measures one native verifier run;
it is not an on-chain CU measurement, an adversarial query budget, or a
security bound. Prover execution is outside the count.
