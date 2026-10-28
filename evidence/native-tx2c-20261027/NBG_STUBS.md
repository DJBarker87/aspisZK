# NBG stub register

No field multiplication is evaluated or proved in Kani. No LPb passing stage is
reused as new closure credit; no cfg-if/libc drift exception is asserted.

| Stub | Paired theorem / retained item | Domain and what caller establishes |
|---|---|---|
| `NBG_runtime::runtime_hashv` for `solana_program::hash::hashv` | `NBC_ReleaseLeaves.digest_result`; `NBG_Runtime.digest_transition`; approved runtime syscall/digest realization | Hash value is arbitrary32-byte reply. Stub asserts identical outer-slice pointer and length, increments a call counter, returns that reply. K005 uses two ordered parts, each arbitrary length0..32 and arbitrary contents; it establishes the descriptor identity and exactly one call. Universal source wrapper association also uses the exact unbranched one-expression frozen body, not an extrapolation of bounded slice tests. Runtime hash state and hash VALUE remain trusted; SHA is never unwound. |

`NBG_Runtime.digest_transition` is a source-shaped state law. It does not
install a dictionary or itself establish a native bridge. Coherent SInt2 uses
op43/op44; no op48/op49 digest/error attribution is made.
